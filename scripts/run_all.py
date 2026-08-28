#!/usr/bin/env python3
"""Run every exact-arithmetic certificate and analytic-lift audit."""

from __future__ import annotations

import subprocess
import sys
import time
import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CERTIFICATES = ROOT / "certificates"
PROGRAMS = (
    "vertex_star_certificate.py",
    "macro_mean_certificate.py",
    "low_degree_bubble_isomorphism.py",
    "p5_two_tet_transfer.py",
    "edge_star_certificate.py",
)
ANALYTIC_AUDITS = (
    "audit_analytic_vertex_lift.py",
    "audit_analytic_edge_lift.py",
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--representatives",
        action="store_true",
        help="run the fast seven-types-per-grid edge smoke test instead of the exhaustive edge run",
    )
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("run certificates without Python -O so assertions remain active")
    if sys.version_info < (3, 10):
        raise RuntimeError("Python 3.10 or newer is required")

    import sympy  # imported here to fail before running a partial suite

    if sympy.__version__ != "1.14.0":
        raise RuntimeError(
            f"expected SymPy 1.14.0 from certificates/requirements.txt, "
            f"found {sympy.__version__}"
        )

    print(f"Python: {sys.version.split()[0]}", flush=True)
    print(f"SymPy: {sympy.__version__}", flush=True)
    suite_started = time.perf_counter()
    for program in ANALYTIC_AUDITS:
        path = ROOT / "scripts" / program
        print(f"\n=== {program} ===", flush=True)
        command = [sys.executable, str(path)]
        if not args.representatives:
            command.append("--all-placements")
        started = time.perf_counter()
        subprocess.run(command, cwd=ROOT, check=True)
        print(f"elapsed: {time.perf_counter() - started:.1f}s", flush=True)

    for program in PROGRAMS:
        path = CERTIFICATES / program
        print(f"\n=== {program} ===", flush=True)
        command = [sys.executable, str(path)]
        if args.representatives and program == "edge_star_certificate.py":
            command.append("--representatives")
        started = time.perf_counter()
        subprocess.run(command, cwd=ROOT, check=True)
        print(f"elapsed: {time.perf_counter() - started:.1f}s", flush=True)

    suffix = ".representatives" if args.representatives else ""
    inspector = ROOT / "scripts" / "inspect_edge_star.py"
    subprocess.run(
        [
            sys.executable,
            str(inspector),
            "--certificate", str(CERTIFICATES / f"edge_star_certificate{suffix}.json"),
            "--summary", str(CERTIFICATES / f"edge_star_certificate{suffix}.summary.json"),
            "--validate",
        ],
        cwd=ROOT,
        check=True,
    )
    vertex_inspector = ROOT / "scripts" / "inspect_vertex_star.py"
    subprocess.run(
        [
            sys.executable,
            str(vertex_inspector),
            "--certificate", str(CERTIFICATES / "vertex_star_certificate.json"),
            "--validate",
        ],
        cwd=ROOT,
        check=True,
    )
    vertex_coverage_audit = ROOT / "scripts" / "audit_vertex_coverage.py"
    subprocess.run(
        [sys.executable, str(vertex_coverage_audit)], cwd=ROOT, check=True
    )
    vertex_algebra_audit = ROOT / "scripts" / "audit_vertex_algebra.py"
    subprocess.run(
        [sys.executable, str(vertex_algebra_audit)], cwd=ROOT, check=True
    )
    coverage_audit = ROOT / "scripts" / "audit_edge_coverage.py"
    subprocess.run([sys.executable, str(coverage_audit)], cwd=ROOT, check=True)
    print(
        f"\nALL EXACT CERTIFICATES PASSED in "
        f"{time.perf_counter() - suite_started:.1f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
