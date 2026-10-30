# tether-may-form — The Minimal Metric Tether, April–May 2026 form

**Author:** Benjamin Frohman (ORCID 0009-0006-7068-3718). Prepared with assistance from Grok, which is not a co-author.
**Status:** local only, not published. Lean `v4.30.0-rc1`, Mathlib `v4.30.0-rc1`.

This repo goes back to the original May 2026 statement, "Uniqueness of the Minimal Metric Tether": a degenerate, symmetric, bilinear minimal metric correction to the Arnold Lie–Poisson bracket,
`B(F,G) = -κ ∫|ω|² ⟨Π_u δF, Π_u δG⟩`. Earlier repos are left untouched as the historical record.

## Dated sources (server dates, America/Chicago)
| Source | Date | Location |
|---|---|---|
| `main3_May03.tex` | May 2 2026, 7:28 PM CDT (Drive); text says April 2026 | Drive copy, `/workspace/drive/main3_May03.tex` |
| vFinal PDF ("Π_u is the L²-orthogonal projection onto the complement of span{u}"; "Π_u(u)=0, hence B(F,H)≡0") | created May 21 2026, 9:37 AM CDT | https://drive.google.com/file/d/1wYNidezKnlLpegfoPGRSu5VSPBHPI8zS |
| Grok AI audit, labelled "referee report" (asks for a "Degeneracy Verification Lemma") | May 21 2026 | `/workspace/drive/referee_0521.txt`; folder https://drive.google.com/drive/folders/1DYIvYRWghrNztxIQzyLYbVbFsN8IaJ_T |
| May 21 email to ai_eng@spacex.com, 3 photos (κ = 1, tanh bound) | May 21 2026, 4:58 PM CDT | Gmail |
| Living document, axioms (A1)–(A5), "uniqueness up to gauge" | docx last modified Jun 26 2026 | `/workspace/drive/living.txt` |
| `Tether.lean` (C1–C3, 5-step uniqueness; `projectionOrthogonalToU` was `sorry`, C3 was `True`) | May 31 2026, 1:32 AM CDT | https://drive.google.com/file/d/1vLWAfj2fA73OfdGvcDj1dx5PkiBwpoUS |

κ: `κ = 1` was the author's May teaching placeholder; `3/2` was introduced Aug 26 2026. Here κ is a free parameter.
Unlike the Aug 26 proof, this file uses **no saturation and no polarization assumptions**.

## What is proved (0 custom axioms; only propext, Classical.choice, Quot.sound)
`TetherMayForm/Basic.lean`, abstract real inner-product-space model:
- `projectionOrthogonalToU : piU u u = 0`, where `piU u := (ℝ ∙ u)ᗮ.starProjection`
- `piU_apply_eq_zero_iff`: the kernel of Π_u is exactly span{u}
- `frohmanianTether_symm`, `frohmanianTether_self_nonpos` (bilinearity holds by construction, as a `LinearMap.BilinForm`)
- `degeneracy_verification`, `frohmanianTether_degenerate`, `frohmanianTether_energy_neutral`: the Degeneracy Verification Lemma (C2)
- `degeneracy_forces_projection`: any symmetric C2 form satisfies B(F,G) = B(Π_u F, Π_u G) (May 31 step 3)
- `frohmanianTether_invariant`: C1, invariance under isometries fixing u
- `gauge_uniqueness_weak`: symmetric + C2 ⇒ B − tether is in the gauge class

- `degeneracy_verification : 𝔗_F[κ, w, u] F (kineticEnergyGradient u) = 0`; `tetheredBracket_kineticEnergy`: {F,H}_TF = {F,H}_classical

## Naming (the author's May naming)
`frohmanianTether` with notation `𝔗_F[κ, w, u]` (main3, May 3: 𝔗_F "Frohmanian Symplectic Tether"; vFinal, May 21: TF).
`tetheredBracket`, written `⦃F, G⦄_𝔗F[classical; κ, w, u]`, is {F,G}_TF = {F,G}_classical + B(F,G), with the classical bracket left as a parameter.
`frohmanian_symplectic_tether_theorem` is the May 30 export name. It now states existence and uniqueness with the concrete C3.

## Notes
- The "referee report" of May 21 (`referee_0521.txt`) was an audit by Grok AI, not a human referee.
- vFinal calls TF an *antisymmetric* correction, but the formula it writes, -κ∫|ω|²⟨Π_u δF, Π_u δG⟩, is *symmetric*. This is an open question for Benjamin. The Lean code follows the written formula.

## C3 — controllable negative feedback (concrete, non-circular)
May wording, (A5): "production of negative quadratic feedback with coefficient fixed by matching"; "(with κ = 1 fixed by exact leading-term matching to the stretching coefficient)"; "This correction is derived by coefficient matching at the spatial maximum of |ω|²".

```lean
structure ProducesControllableNegativeFeedback (κ w : ℝ) (u : H)
    (B : LinearMap.BilinForm ℝ H) : Prop where
  nonpos : ∀ F, B F F ≤ 0
  calibrated : ∃ e : H, ⟪u, e⟫ = 0 ∧ ‖e‖ = 1 ∧ B e e = -(κ * w)
```
**Candour:** C3 is a *one-direction normalization*: it fixes B on a single unit vector ⟂ u. The Aug 26 saturation hypothesis fixed B(F,F) for *all* F, which is already the conclusion. Here, extending from one direction to all is proved (C1 + C2, Schur step); C3 contributes only the scalar κw, by matching — as the May text says. `nonpos` is not needed for uniqueness (it holds for the tether when κ,w ≥ 0).

## Uniqueness (proved, 0 sorry)
- `admissible_eq_smul_frohmanianTether`: dim ≥ 3, symmetric + C1 + C2 ⇒ `B = 𝔗_F[c, 1, u]`.
- `feedback_fixes_coefficient`: C3 ⇒ `c = κ*w` (the former `hC3fix`, now a lemma).
- `uniqueness_of_minimal_metric_tether_iff` (unconditional):
  `3 ≤ finrank ℝ H → 0 ≤ κ → 0 ≤ w → u ≠ 0 → (IsAdmissibleCorrection u (ProducesControllableNegativeFeedback κ w u) B ↔ B = 𝔗_F[κ, w, u])`.
- `frohmanian_symplectic_tether_theorem_calibrated`: existence ∧ uniqueness, one-direction C3 (kept for comparison). The main theorem now uses Route A — see below.
- `uniqueness_of_minimal_metric_tether`: general form for any C3 with `hC3fix`.

## κ
κ is a free parameter. κ = 1 was the May teaching placeholder; 3/2 came in Aug 26 2026.

## Still open (as content, not sorry)
- ∫|ω|² is collapsed to a scalar w; C1 is modelled by linear isometries fixing u, not the coadjoint action.
- "Antisymmetric" vs. the symmetric formula (see Notes).

## History, timeline, provenance
`docs/timeline.md`, `docs/provenance_appendix.md`, `history/` (verbatim excerpts, May 21 photos).

## License
Apache-2.0 (`LICENSE`), with `NOTICE`. Grok assisted; it is not an author.

Run `lake build`, then `lake env lean scripts/Axioms.lean`. The output is saved in `axioms_output.txt`.

## Oct 29 2026 additions
* `TetherMayForm/Metriplectic.lean` — unique split B = B_sym + B_anti, alternating
  antisymmetric part, trace-pairing orthogonality, C2 for the parts (needs two-sided
  degeneracy `B u F = 0` too), metriplectic bracket `P + 𝔗_F` and energy conservation.
* `TetherMayForm/RouteA.lean` — C3 in the May 20 Route A form; `uniqueness_routeA_iff`.
  The old one-direction C3 is kept as the weaker variant (`RouteAFeedback.toControllable`).
* `TetherMayForm/Layer2.lean` — Young absorption with ε = κ/4, equilibria, and the
  comparison bound y ≤ max(y(0), C/κ'').

**Caveats.** Layer 2 is a real-variable theorem about any function obeying the
differential inequality; deriving that inequality from Navier–Stokes is *not* formalized,
and no Navier–Stokes regularity is claimed. The 9-term Jacobi expansion is now formalized in an algebraic
model (`Jacobi.lean`, below). κ is fixed by matching to a supplied stretching coefficient S; S = C_CZ(3)
is not derived. The May 21 text calls the tether's coefficient κ = C_CZ(3); the slide/
build_context use ε = κ/4 for absorption.

## Main theorem — κ derived by Route A matching (`TetherMayForm/Main.lean`)
C3 (Route A, May 20 2026), `RouteAFeedback S w u ω B`: `B(F,F) ≤ 0` for all F; ω ⟂ u, ‖ω‖ = 1
(the maximizer direction of |ω|²); the leading quadratic coefficient at the maximum,
`leadingCoefficient S w ω B = S·w + B(ω,ω)`, is zero (the feedback cancels the stretching);
and B has no antisymmetric part on uᗮ. **There is no calibration constant.** κ is
*derived*: `routeA_determines_kappa : w ≠ 0 → RouteAFeedback S w u ω 𝔗_F[κ,w,u] → κ = S`.

```lean
theorem frohmanian_symplectic_tether_theorem [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) {S w : ℝ} (hS : 0 ≤ S) (hw : 0 < w) (u ω : H)
    (hu : u ≠ 0) (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔
      ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u]
```
Layer 1 → Layer 2: `routeA_layer2_bound` — with κ = S from matching, ε = κ/4 and
κ'' = κ/2 − C_abs > 0, any y ≥ 0 with y' ≤ C y² − κ'' y³ stays ≤ max(y(0), C/κ'').

## 9-term Jacobi on the reduced orbit (`TetherMayForm/Jacobi.lean`)
Model: {a,b}_{𝔗_F} = P(a,b) + T(a,b), with P a classical bracket (additive in the first slot,
satisfies Jacobi) and T(a,b) = 𝔗_F[κ,w,u](a,b)·u. Proved:
- `jacobiator_nine_terms`: Jacobiator = 3 classical + 3 mixed + 3 tether–tether terms.
- `jacobi_classical_cancel`: the 3 classical terms cancel.
- `jacobi_term7/8/9`: each tether–tether term is 0 (because Π_u u = 0).
- `jacobiator_eq_mixed`, `jacobi_iff_mixed_cancel`: Jacobi holds on any set R (e.g. uᗮ)
  **iff** the 3 mixed terms cancel there. This is the exact condition.
- `jacobiator_eq_zero_of_central`: sufficient condition — u central for P (P(u,·) = 0),
  P homogeneous in the first slot, and Π_u(P(a,b)) = 0.

**Plainly:** the Jacobi identity is *not* proved unconditionally. The tether is symmetric,
so {·,·}_{𝔗_F} is a metriplectic bracket, not a Poisson bracket; Jacobi holds only when
the mixed terms cancel. Its Poisson part is unchanged on uᗮ (`RouteAFeedback.poisson_unchanged`).

## Scope and open items
- **Tethered vs. true Navier–Stokes.** `Torus.lean` defines velocity fields on 𝕋³ (1-periodic
  on `EuclideanSpace ℝ (Fin 3)`), curl/vorticity, divergence, Laplacian, advection, the NS
  equation via `fderiv`, `C^∞` smoothness on `[0,T)×𝕋³`, `y(t) = sup|ω(t,x)|`, and
  `toNSTetherSolution` (`SmoothOn T` := classical solution on `[0,T)`; monotone, `SmoothOn 0`,
  `y ≥ 0` proved). `IsTrueNS` (no forcing) and `IsTetheredNS` (forcing = a 𝔗_F feedback field,
  a MODIFIED system) are kept separate. How 𝔗_F[κ,w,u] becomes a vector field on 𝕋³ is not
  formalized (`TetherRealizesFeedback`, provably false for true NS).
- **The 𝔗_F term.** `frohmanianTether_orth_self`: 𝔗_F[κ,w,u](ω,ω) = −κw‖ω‖² for ω ⟂ u.
  Here `w` is the scalar weight of 𝔗_F, not the vorticity ω. The `−κy⁴` damping needs the
  quartic weight `w = y²` (`QuarticWeight`), an explicit hypothesis: C1–C3 fix the shape
  and κ = S, never `w`. With constant `w` only `−κwy²` follows.
- **Named hypotheses (never `axiom`):** `BKMContinuation` (Beale–Kato–Majda, CMP 94 (1984)
  61–66; stated in a weaker sup-bound form implied by BKM), `LocalContinuation` (Fujita–Kato,
  ARMA 16 (1964); Kato, Math. Z. 187 (1984)), `EnergyIdentity`, `StretchingCZ` (stronger than
  known: the L∞ CZ bound has a log loss, Kozono–Taniuchi CMP 214 (2000)), `ViscousAtMax`
  (maximum principle), `CrossControlled` (model assumption), `TetherFeedbackOf` +
  `QuarticWeight`, and `NSTetherEnstrophyInequality`.
- The model step "leading coefficient at the maximum = S·w + B(ω,ω)" is assumed, not derived
  from Navier–Stokes. S = C_CZ(3) is not derived. No Navier–Stokes regularity is claimed.
- Layer 2's differential inequality is a hypothesis.
- ∫|ω|² is collapsed to a scalar w. C1 uses linear isometries fixing u, not the full coadjoint action.
- Jacobi: only the algebraic vector-valued model is covered. Brackets on functionals
  (functional derivatives) are not formalized. Full vanishing is conditional, as stated above.
- "Antisymmetric" (vFinal wording) vs. the symmetric written formula is still open.

## Build
Mathlib is pinned in `lake-manifest.json` (Lean `v4.30.0-rc1`). After a fresh clone:
`lake exe cache get && lake build && lake env lean scripts/Axioms.lean`.
96 theorems, 0 sorry, axioms only propext / Classical.choice / Quot.sound (`axioms_output.txt`).
Author: Benjamin Stanley Frohman <frohmanbenjamin@gmail.com>, ORCID 0009-0006-7068-3718.

## Final.lean (local): assumption status
- `QuarticWeight`: **redefined**. The tethered-system weight is now part of the definition: `quarticTether κ u ω := 𝔗_F[κ, ‖ω‖², u] ω ω`. This follows the May `S_ε = ∫(½ω_ε² − (κ/2)ω_ε⁴ϕ_ε)`, "quartic term weighted by |ω|²". The May sources never derive this weight from C1–C3.
- `ViscousAtMax`: **proved** (second-derivative test + `⟪v,v''⟫ ≤ −‖v'‖²` along each coordinate line at a max of ‖ω‖).
- Maximizer of ‖ω(t,·)‖ on 𝕋³: **proved** for continuous periodic fields (`periodic_exists_max`).
- Still cited hypotheses: `NSTetherEnstrophyInequality`, `BKMContinuation`, `LocalContinuation`, `EnergyIdentity`, `StretchingCZ` (pure L∞ form is stronger than known), `CrossControlled`, `TetherFeedbackOf`/`TetherRealizesFeedback`.

## Status update — log-loss stretching (LOCAL, `LogLoss.lean`)

* `StretchingCZ` (`ω·Sω ≤ C y³`) is **deprecated**: false as an L∞ estimate. Replaced by
  `StretchingByStrain` (`ω·Sω ≤ ‖S‖∞ y²`) and `BKMLogInequality`
  (`‖S‖∞ ≤ C(1 + ‖ω‖_{L²} + y·log(e + ‖ω‖_{Hˢ}))`, s > 3/2; Beale–Kato–Majda, CMP 94 (1984)
  61–66; Brezis–Gallouët, Nonlinear Anal. 4 (1980) 677–681; Kozono–Taniuchi, CMP 214 (2000)
  191–200).
* Tethered system (quartic 𝔗_F feedback): `y' ≤ C(1+Z0) y + C log(e+Z) y² − κ'' y³`
  (`tether_pointwise_logloss`). Cubic damping dominates (`logField_neg_above`), giving
  `y ≤ max(y₀, B/κ'' + √(A/κ''))` with `A = C(1+Z0b)`, `B = C log(e+Zb)`
  (`comparison_bound_logloss`), and `global_regularity_logloss`.
* **Remaining hypothesis `HigherNormControl`**: an a priori bound on `‖ω‖_{Hˢ}` and `‖ω‖_{L²}`
  up to the first possible singular time. This is **circular** (Hˢ ⊂ L∞ already bounds y).
  The Hˢ energy estimate does not remove it: with `L = log(e+‖ω‖_{Hˢ})`, Kato–Ponce plus the
  BKM log inequality give `L' ≤ C(1+Z0+yL)`, and the y-bound is only `y ≲ L`, so
  `L' ≲ a + bL²` (Riccati, may blow up in finite time). The tether's Hˢ contribution has a
  damping leading term but commutators of the same order `~ y²‖ω‖²_{Hˢ}` with no sign, so it
  does not close the loop either. Closing needs y bounded independently of the Hˢ norm.
* Still: this is about the **tethered** system only; `nsOnly_not_sufficient` stands for true NS.

## Enstrophy (L²) bound — TETHERED system (`TetherMayForm/EnstrophyL2.lean`)

`E = ½‖ω‖₂²`, `Q = ‖ω‖₄⁴`, unit torus. Quartic tether `quarticTether κ u ω = 𝔗_F[κ, ‖ω‖², u] ω ω = −κ‖ω‖⁴`.

Proved (0 sorry, standard axioms only):
- `tethered_enstrophy_gronwall`: `E(t) ≤ E(0)·exp((C²/2κ) t)`.
- `tethered_enstrophy_uniform`: `E(t) ≤ max(E(0), C²/(2κ²))`, uniform in time (uses `E' ≤ (C²/κ)E − 2κE²`).
- `tethered_L2_vorticity_bounded`: `‖ω‖₂` bounded uniformly — this discharges the **L² (`Z0`) part** of
  `HigherNormControl` *for the tethered system, given the cited inputs below*.

Named cited inputs (stated, not derived in Lean): `TetheredEnstrophyIdentity` (`E' = ∫ω·Sω − ν‖∇ω‖₂² − κ‖ω‖₄⁴`),
`StrainL2Bound` (Hölder + L² Biot–Savart `‖∇u‖₂ = ‖ω‖₂`, Parseval; Majda–Bertozzi), `L4L2Holder`.

**Plain Navier–Stokes:** the `−κ‖ω‖₄⁴` term is absent, nothing absorbs `∫ω·Sω`, and this argument does not close.
**Circularity:** the `Hˢ` (`Zb`) part of `HigherNormControl` is untouched; regularity is still conditional on it.
