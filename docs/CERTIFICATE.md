# Kernel Certificate Status

**GitHub repository**: https://github.com/BenFrohman/four-frontiers-boundary-markers

**DOI**: [10.5281/zenodo.24546175](https://doi.org/10.5281/zenodo.24546175)

**ORCID**: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)

## Current status

- `Fourfrontiers/Curve3936b1TrivialTorsion.lean` (or equivalent) is **not present** in the repository.
- The torsion statement \(E(\mathbb{Q})_{\mathrm{tors}} = \{O\}\) for \(y^2 = x^3 - x^2 - 12\) therefore remains **uncertified**.
- The CI workflow (`.github/workflows/lean.yml`) is configured to run `lake build`, zero-sorry/admit/axiom check, and `#print axioms` once the modules are present.
- A green CI log will be attached to the Zenodo record when available.

## Certified markers that are present

- Sextic Jacobian numbers
- Incidence dimension arithmetic
- Height growth bound (in `HeightDuplication.lean`)

Copyright (c) 2026 Benjamin Stanley Frohman. Apache License 2.0.
