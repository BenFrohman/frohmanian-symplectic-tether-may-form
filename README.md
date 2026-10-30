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
- `frohmanian_symplectic_tether_theorem`: existence ∧ uniqueness, same hypotheses.
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
