#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean scripts/CheckAxioms.lean
lake env lean --run scripts/CheckStatements.lean
lake env lean scripts/CheckLint.lean
