#!/usr/bin/env python3
"""Check this project's Palomar layout and metadata consistency (not Comparator)."""
import json
import os
from pathlib import Path
import re
import sys
import tomllib

import yaml

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


class StrictLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node, deep=False):
    result = {}
    for key_node, value_node in node.value:
        if key_node.tag == "tag:yaml.org,2002:merge":
            raise ValueError("YAML merge keys are not allowed")
        key = loader.construct_object(key_node, deep=deep)
        if key in result:
            raise ValueError(f"duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


StrictLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def text(path):
    return (ROOT / path).read_text(encoding="utf-8")


def without_comments(source):
    # Nested Lean block comments and line comments; preserve line breaks.
    result = []
    depth = 0
    i = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    result.append("\n")
                i += 1
        elif quoted:
            result.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
                continue
            if source[i] == '"':
                quoted = False
            i += 1
        elif pair == "/-":
            depth = 1
            result.append(" ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            if source[i] == '"':
                quoted = True
            result.append(source[i])
            i += 1
    require(depth == 0, "unterminated Lean block comment")
    return "".join(result)


def main():
    config = json.loads(text("comparator.json"))
    require(set(config) <= {"challenge_module", "solution_module", "theorem_names",
                           "definition_names", "permitted_axioms", "enable_nanoda"},
            "comparator.json has unsupported fields")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "unexpected Challenge/Solution module names")
    names = config["theorem_names"]
    require(names and len(names) == len(set(names)), "compared theorem names must be nonempty and unique")
    require(set(config["permitted_axioms"]) == ALLOWED, "incorrect permitted axioms")
    require(config.get("definition_names", []) == [], "this submission has no definition holes")
    challenge = text("Challenge.lean")
    require(len(challenge.encode("utf-8")) <= 100 * 1024, "Challenge exceeds 100 KiB")
    require(len(challenge.splitlines()) <= 1000, "Challenge exceeds 1,000 lines")
    clean = without_comments(challenge)
    require(re.findall(r"^(?:public )?import (.+)$", clean, re.M) == ["Mathlib"],
            "Challenge must import only Mathlib")
    declared = ["NairTenenbaum.Submission." + n for n in re.findall(r"^theorem (\w+) :", clean, re.M)]
    require(declared == names, "Challenge theorems and Comparator configuration disagree")
    require(len(re.findall(r"\bsorry\b", clean)) == len(names),
            "Challenge must have exactly one deliberate placeholder per theorem")
    require(not re.search(r"\b(axiom|native_decide)\b", clean), "unexpected Challenge axiom or native_decide")

    metadata = yaml.load(text("formalization.yaml"), Loader=StrictLoader)
    require(metadata["version"] == "v0.4", "metadata must use v0.4")
    project = metadata["project"]
    for field, limit in [("name", 300), ("description", 10000)]:
        require(isinstance(project[field], str) and 0 < len(project[field]) <= limit,
                f"invalid project.{field}")
    for field in ["authors", "responsible_maintainers"]:
        require(project[field] and all(isinstance(n, str) and n.strip() for n in project[field]),
                f"invalid project.{field}")
    require(project["license"] == "Apache-2.0", "project license must match LICENSE")
    licenses = [p for p in ROOT.iterdir() if re.fullmatch(
        r"(?i)(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?", p.name)]
    require(licenses == [ROOT / "LICENSE"], "exactly one conventional LICENSE file is required")
    require(not licenses[0].is_symlink(), "LICENSE may not be a symbolic link")
    require("Apache License" in text("LICENSE") and "Version 2.0, January 2004" in text("LICENSE"),
            "LICENSE must contain Apache-2.0 license text")
    require(metadata["classification"]["arxiv"] == ["math.NT"], "unexpected arXiv classification")
    codes = metadata["classification"]["msc2020"]
    require(0 < len(codes) <= 8 and len(codes) == len(set(codes)), "invalid MSC classification list")
    require(metadata["sources"] and all(s["title"] and s["id"] and s["relationship"]
                                        for s in metadata["sources"]), "incomplete sources")
    require(metadata["automation"]["methods"] and metadata["review"]["status"],
            "automation and review metadata are required")
    require(metadata["status"]["sorry_count"] == metadata["status"]["sorry_in_definitions"] == 0,
            "proof development must have no unresolved holes")
    require(set(metadata["status"]["axioms"]) == ALLOWED, "metadata axiom list disagrees")
    require([s["lean"] for s in metadata["alignment"]["statements"]] == names,
            "metadata alignment and Comparator configuration disagree")
    require([s["declaration"] for s in metadata["status"]["main_results"]] == names,
            "metadata main results and Comparator configuration disagree")
    require((ROOT / "formalization.yaml").stat().st_size <= 256 * 1024, "metadata exceeds 256 KiB")

    lake = tomllib.loads(text("lakefile.toml"))
    require(not (ROOT / "lakefile.lean").exists(), "only one Lake configuration is allowed")
    require({"NairTenenbaum", "Challenge", "Solution"} <= set(lake["defaultTargets"]),
            "all submission libraries must be default targets")
    require(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", text("lean-toolchain").strip()),
            "toolchain must be pinned to a release")
    for package in json.loads(text("lake-manifest.json"))["packages"]:
        require(package["type"] == "git", "this project must have only pinned Git dependencies")
        require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]), "dependency is not pinned to a full SHA")
        require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"]),
                "dependency must use a public credential-free GitHub URL")

    count = 0
    for directory, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git"}]
        for filename in files:
            path = Path(directory) / filename
            if path.suffix != ".lean":
                continue
            require(not path.is_symlink(), f"Lean source symlink: {path}")
            source = path.read_text(encoding="utf-8")
            require(len(source.splitlines()) <= 10000, f"source exceeds 10,000 lines: {path}")
            stripped = without_comments(source)
            require(stripped.lstrip().startswith("module\n"), f"missing module header: {path}")
            if path != ROOT / "Challenge.lean":
                require(not re.search(r"\b(sorry|admit|native_decide)\b|^axiom\s", stripped, re.M),
                        f"unexpected proof hole or axiom: {path}")
            count += 1
    print(f"Submission preflight passed: {len(names)} compared theorems, {count} Lean source files; "
          f"Challenge {len(challenge.splitlines())} lines / {len(challenge.encode('utf-8'))} bytes.")
    print("This checks local layout and consistency; it does not replace Comparator or Palomar verification.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, yaml.YAMLError) as error:
        print(f"submission preflight failed: {error}", file=sys.stderr)
        sys.exit(1)
