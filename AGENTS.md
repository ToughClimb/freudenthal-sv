# Repository rules

- Keep this repository limited to exact-verification source, deterministic
  certificate data, inspection scripts, and public reproducibility
  documentation.
- Never commit credentials, private contact data, machine-specific absolute
  paths, local logs, review correspondence, manuscript drafts, third-party
  papers, or generated Python caches.
- Preserve exact arithmetic. Do not replace rational calculations with
  floating-point tolerances or randomized checks.
- Do not edit generated certificate JSON by hand. Regenerate it with the
  corresponding certificate program and validate its schema and record counts.
- When mathematical artifacts change, run the representative suite at minimum,
  run the full suite before a release, and update `SHA256SUMS`.
- Keep the analytic proof and the computational checks conceptually distinct:
  the code provides additional verification and reproducibility support.
- Preserve the repository's `GPL-3.0-or-later` licensing statement. Because
  generated certificates record generator hashes, do not add or alter source
  headers without regenerating and revalidating the affected records.
