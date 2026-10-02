#!/usr/bin/env bash
set -euo pipefail

formalization_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$formalization_root"

scripts/lakew env lean --version
scripts/lakew build
scripts/lakew env lean FreudenthalSVLean/TrustAudit.lean

printf '%s\n' 'All encoded modules and the whole-project axiom audit passed.'
printf '%s\n' 'The unconditional uniform right-inverse theorems for k=4,5 on all N>=1 passed.'
printf '%s\n' 'Full H1-energy bounds and uniform reduced inf-sup witnesses passed.'
printf '%s\n' 'The higher-degree extension is outside the claimed formalization scope.'
