# Publication note: provenance of the Riccati / cubic-absorption comparison ODE

**Author of the mathematical content:** Benjamin Stanley Frohman.
**Scope:** provenance only. This note makes no claim about the Clay Millennium Problem. Everything formalized here concerns a scalar comparison ODE or the *tethered* (modified) system. It says nothing about the regularity of plain Navier–Stokes. Not peer reviewed.
**Excluded:** I did not use any material by Félix Robles.

## 1. Sources, earliest first
- **2026-05-18 and 2026-05-21 (self-dated drafts, unpublished).** The author's drafts state the comparison ODE `y' = C y² − κ'' y³` and say the cubic term comes from quartic absorption. The drafts described this bound as governing "global regularity"; that wording was an overstatement. The bound applies only to the tethered comparison ODE, as stated in §3.
- **2026-06-19 (earliest git timestamp, unpublished repository of the author).** The same ODE, its equilibria `0` and `y* = C/κ''`, and the bound `y ≤ max(y(0), y*)` appear in the author's code and notes.
- **2026-10-07, `BenFrohman/Clay-`** (`lean/Clay/Gaps/ConditionalRiccati.lean`): `conditional_riccati`, a conditional statement whose hypothesis `CorrectedMaxRate` is open.
- **Later (August–October 2026, unpublished).** Further restatements of the same comparison ODE.

The self-dated drafts and unpublished repositories are not included here. Their dates come from the documents themselves and from the author's private git history, and they cannot be checked independently from this repository.

## 2. Side by side with this repository

| Author's original | Lean (this repo) | companion.tex |
|---|---|---|
| `y' = C y² − κ'' y³` (May 2026) | `Layer2.comparisonField` | §Layer 2, §Riccati |
| equilibria `0`, `y* = C/κ''`; `M ≤ max(M(0), y*)` | `Layer2.comparison_bound`, `Riccati.tethered_ceiling` | §Riccati |
| pure Riccati envelope vs. cubic damping | `Riccati.ricSol`, `ricSol_hasDerivAt`, `riccati_blowup` | §Riccati |
| quartic absorption → cubic damping | `EnstrophyL2.enstrophy_deriv_logistic`, `tethered_enstrophy_uniform` | Result 2 |
| log-loss variant | `LogLoss.logThreshold`, `comparison_bound_logloss` | Result 2 |

**What is new here:** the L² enstrophy form `E' ≤ (C²/κ)E − 2κE²` and its cap `C²/(2κ²)`. Its earliest commit is in this repository (2026-10-29).

## 3. What is machine-checked
These are kernel-checked with the standard axioms only (see `AXIOMS.md`):
- `riccati_blowup`: the plain Riccati equation `y' = C y²` with `C, y0 > 0` has the solution `y0/(1 − C y0 t)`, which exceeds every bound before `T* = 1/(C y0)`.
- `tethered_ceiling`: under `y' ≤ C y² − κ'' y³` with `κ'' > 0`, `y ≤ max(y(0), C/κ'')` for all time.

Both are scalar ODE facts. Neither says anything about the regularity of plain 3-D Navier–Stokes, which remains open.

## 4. Addendum: the 4/3 exponent comes from interpolation
The exponent 4/3 is an interpolation and Young exponent, not a bracket coefficient. It enters at the H¹ rung: Gagliardo–Nirenberg/Sobolev gives `N ≤ A G^{1/4} L^{3/2}`, and Young's inequality is then applied with exponents (4, 4/3) (`PalinstrophyH1.lean`, companion.tex §Result 2). The field-level bracket coefficients are 3/2 and 3i/8 (`FieldJacobi.lean`).
