# tether-may-form: the Frohmanian Symplectic Tether 𝔗_F and a cubically damped Navier–Stokes model

**Author:** Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718), <frohmanbenjamin@gmail.com>. Prepared with assistance from Grok, which is not a co-author.
**Status:** private, not published. Lean `v4.30.0-rc1`, Mathlib `v4.30.0-rc1`.

This repo has **two separate results**. Keep them apart.

| | Result 1: the original tether | Result 2: the damped model |
|---|---|---|
| System | plain Navier–Stokes; 𝔗_F is a bracket correction | Navier–Stokes **plus** an added force −κ curl⁻¹P(\|ω\|²ω) |
| Does 𝔗_F change the dynamics? | **No.** The Leray projection removes it | **Yes.** That is the point of the model |
| Navier–Stokes regularity | **open**, not claimed | global smoothness proved **for this modified system**, given cited classical inputs |

Neither result is, or claims to be, a solution of the Navier–Stokes Millennium Problem for the unmodified equations.

---

## Result 1: The Frohmanian Symplectic Tether (original design)

`𝔗_F[κ, w, u](F, G) = −(κw)⟪Π_u F, Π_u G⟫`, where Π_u is the orthogonal projection onto the complement of span{u} and w is the scalar weight (in the May drafts, ∫|ω|²). The tethered bracket is {F,G}_TF = {F,G}_classical + 𝔗_F(F,G) (`tetheredBracket`). Abstract real inner-product-space model, `Basic.lean`, `RouteA.lean`, `Main.lean`, `Metriplectic.lean`, `Jacobi.lean`.

**Proved (0 sorry):**
- **Degeneracy lemma (C2):** `projectionOrthogonalToU` (Π_u u = 0), `degeneracy_verification` (𝔗_F[κ,w,u] F (kineticEnergyGradient u) = 0), `frohmanianTether_degenerate`, `frohmanianTether_energy_neutral`, `tetheredBracket_kineticEnergy` ({F,H}_TF = {F,H}_classical), `degeneracy_forces_projection`.
- **Uniqueness theorem:** `admissible_eq_smul_frohmanianTether` (dim ≥ 3, symmetric + C1 invariance + C2 ⇒ B = 𝔗_F[c,1,u]); `uniqueness_of_minimal_metric_tether_iff`; `gauge_uniqueness_weak`.
- **Route A, κ = S:** `RouteAFeedback` (May 20 form: the feedback cancels the leading stretching coefficient S·w + B(ω,ω) = 0 at the maximizer direction). `routeA_determines_kappa` (κ = S), `uniqueness_routeA_iff`, and the main theorem `frohmanian_symplectic_tether_theorem`: `IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u]`. There is no calibration constant. S = C_CZ(3) is supplied, not derived.
- **Metriplectic split:** `split_unique`, `symPart_frohmanianTether`, `antiPart_frohmanianTether` (𝔗_F is purely symmetric), `metriplecticBracket_split`, `metriplectic_energy_conserved`.
- **9-term Jacobi:** `jacobiator_nine_terms`, `jacobi_classical_cancel`, `jacobi_term7/8/9` (tether–tether terms vanish because Π_u u = 0), `jacobi_iff_mixed_cancel` (Jacobi holds **iff** the 3 mixed terms cancel), `jacobiator_eq_zero_of_central` (a sufficient condition). Jacobi is **not** unconditional: 𝔗_F is symmetric, so the bracket is metriplectic, not Poisson.

**The tether is invisible to the dynamics.** In the May drafts the Leray projection is designed to remove the tether correction: "the full tether flow thus reproduces the exact momentum equation" (`main.tex__key_extracts.txt`). The October notes say the tether "does not add a damping term to the PDE itself", and that deriving cubic damping from the unmodified equation "remains an open mathematical problem" (`main.tex`, `CubicSourceGap.tex`, `STATUS-2026-10-10.md`). So **plain Navier–Stokes regularity stays open** under this design.

**Where κ = 0 breaks:** `nsOnly_not_sufficient` (`Enstrophy.lean`) shows that without the tether term, the pointwise inequality at the vorticity maximum has no cubic damping and the comparison argument does not close. `tetheredNS_zero_iff` / `tetheredVorticity_zero_iff` show that κ = 0 is exactly plain Navier–Stokes. The uniform L² bound of Result 2 is the first step that fails at κ = 0.

**Open in Result 1:** ∫|ω|² is collapsed to a scalar w; C1 uses linear isometries fixing u, not the full coadjoint action; vFinal calls 𝔗_F "antisymmetric" but the written formula is symmetric (Lean follows the formula); brackets on functionals are not formalized; the quartic weight w = ‖ω‖² is **not** forced by C1–C3 (they fix the shape and κ only).

---

## Result 2: Global regularity for a cubically damped Navier–Stokes model motivated by the Frohmanian tether

This is a **modified** fluid model, not ordinary Navier–Stokes. On the unit torus 𝕋³, with ν > 0 and κ > 0, P the Leray projection, and curl⁻¹ the Biot–Savart inverse:

- **Velocity form** (`IsTetheredNSQuartic`, i.e. `Torus.IsTetheredNS` with this force):
  ∂ₜu + (u·∇)u + ∇p = νΔu − κ curl⁻¹P(|ω|²ω), div u = 0, ω = curl u.
- **Vorticity form** (`IsTetheredVorticityEq`):
  ∂ₜω + (u·∇)ω = (ω·∇)u + νΔω − κP(|ω|²ω).
- **Link:** `curl_lerayTetherForce` (curl of the force = −κP(|ω|²ω)); `tetheredVorticity_of_velocity` (velocity form ⇒ vorticity form).
- **Tie to 𝔗_F:** the pointwise density −κω·(|ω|²ω) = `quarticTether κ u ω` = 𝔗_F[κ, ‖ω‖², u](ω, ω) = −κ‖ω‖⁴ (`quarticTether_eq`, `quarticTether_density`). The quartic weight w = ‖ω‖² is **part of the model's definition**, following the May S_ε functional; it is not derived.

**Proved in Lean (0 sorry), for this system:**
- **L² (enstrophy):** `tether_L2_term` (∫ω·P(|ω|²ω) = ‖ω‖₄⁴), `enstrophyIdentity_of_vorticityLevel`, `tethered_enstrophy_gronwall`, `tethered_enstrophy_uniform` (E(t) ≤ max(E(0), C²/(2κ²)) for all t), `tethered_L2_vorticity_bounded`.
- **H¹ (palinstrophy):** `tether_H1_density_eq` / `tether_H1_density_nonneg` (∇ω:∇(|ω|²ω) = |ω|²|∇ω|² + ½|∇|ω|²|² ≥ 0, any orientation), `tether_H1_term`, `tethered_palinstrophy_gronwall` (‖∇ω(t)‖₂² ≤ ‖∇ω(0)‖₂² e^{Kt}).
- **Higher norm and global:** `higherNormControl_tethered` (`HigherNormControl` follows from the L² and H¹ bounds plus `H1ToHsBootstrap`), `tether_pointwise_logloss`, `comparison_bound_logloss`, `global_regularity_logloss` (global smoothness from the log-loss inequality), plus the older `global_regularity` / `routeA_layer2_bound` / `layer2_bound`.
- **Supporting:** `viscous_nonpos_at_max` / `viscousAtMax_of_max` (maximum principle), `periodic_exists_max` (maximizer of |ω| on 𝕋³).

**Also formalized:** `ChevalleyEilenberg.lean` — CE differentials `d1`/`d2`, `d2_d1` (d∘d = 0 via Jacobi), the antisymmetric correction `antiCorr` (always alternating; cocycle iff `d2 = 0`, automatic for coboundaries: `cocycle_of_coboundary`), `symPart_not_cochain` (the symmetric 𝔗_F part is not a CE cochain); the T³ shear `shear_divFree` for `(sin y,0,0)` and `shearBad_not_divFree` for `(sin x,0,0)`.

**Remaining cited inputs (named `Prop` hypotheses, never `axiom`):**

| Prop | Content | Citation |
|---|---|---|
| `CurlRightInverse` | Biot–Savart: curl⁻¹ inverts curl on admissible fields. **Partially discharged:** `BiotSavart.curlRightInverse_trig` proves it for `curlInvTrig` on finite sums of div-free Fourier modes (`AdmTrig`), with `curl_bsMode`, `div_bsMode`, coefficient-level `bsC_unique`/`gradL2_mode`. Still open: the general smooth periodic case (Fourier series convergence on 𝕋³ + Parseval) | Majda–Bertozzi, *Vorticity and Incompressible Flow* (2002), ch. 2 |
| ~~`CurlOfForcedNS`~~ | **Discharged:** `CurlNS.curlOfForcedNS` (on `t ∈ (0,T)`; Schwarz symmetry + `curl_advection`) | Majda–Bertozzi (2002), ch. 1 |
| `TetheredEnstrophyIdentity` | E′ = ∫ω·Sω − ν‖∇ω‖₂² − κ‖ω‖₄⁴ (supplied via `enstrophyIdentity_of_vorticityLevel` from the classical energy identity) | standard energy method; Majda–Bertozzi (2002) |
| `StrainL2Bound` | Hölder + ‖∇u‖₂ = ‖ω‖₂ (Parseval) | Majda–Bertozzi (2002) |
| `L4L2Holder` | (2E)² ≤ ‖ω‖₄⁴ on the unit torus | Hölder's inequality |
| `TetheredH1Identity` | palinstrophy energy identity for the damped system | standard energy method |
| `NonlinH1Bound` | Hölder + Sobolev + Gagliardo–Nirenberg bound on the stretching term | Gagliardo (1959), Nirenberg (1959) |
| `H1ToHsBootstrap` | H¹ bound ⇒ Hˢ bound, s = 2 > 3/2 | classical for plain NS (Temam, *NS Equations and Nonlinear Functional Analysis*); for the cubic damping this is a standard energy estimate, **not** a published result for this system |
| `StretchingByStrain`, `BKMLogInequality` | ω·Sω ≤ ‖S‖∞y²; ‖S‖∞ ≤ C(1 + ‖ω‖₂ + y log(e + ‖ω‖_{Hˢ})) | Beale–Kato–Majda, CMP 94 (1984) 61–66; Brezis–Gallouët, Nonlinear Anal. 4 (1980) 677–681; Kozono–Taniuchi, CMP 214 (2000) 191–200 |
| `BKMContinuation` | sup-bound form of BKM continuation | Beale–Kato–Majda (1984) |
| `LocalContinuation` | local existence and continuation | Fujita–Kato, ARMA 16 (1964); Kato, Math. Z. 187 (1984) |

**Earlier pointwise route (superseded, kept for the record):** `EnergyIdentity`, `CrossControlled` (model assumption, no source derives it), `TetherFeedbackOf` / `TetherRealizesFeedback` (`not_tetherRealizesFeedback_zero`: provably false for true NS), `NSTetherEnstrophyInequality`, and the deprecated `StretchingCZ` (ω·Sω ≤ Cy³, **false** as an L∞ estimate, replaced by the log-loss form above).

**Plain Navier–Stokes:** with κ = 0 the −κ‖ω‖₄⁴ term is absent, nothing absorbs ∫ω·Sω, and the uniform L² bound fails. None of Result 2 carries over.

---

## Dated sources (server dates, America/Chicago)
| Source | Date | Location |
|---|---|---|
| `main3_May03.tex` | May 2 2026, 7:28 PM CDT (Drive) | `/workspace/drive/main3_May03.tex` |
| vFinal PDF | created May 21 2026, 9:37 AM CDT | https://drive.google.com/file/d/1wYNidezKnlLpegfoPGRSu5VSPBHPI8zS |
| Grok AI audit labelled "referee report" (not a human referee) | May 21 2026 | `/workspace/drive/referee_0521.txt` |
| May 21 email to ai_eng@spacex.com, 3 photos | May 21 2026, 4:58 PM CDT | Gmail |
| Living document, axioms (A1)–(A5) | docx last modified Jun 26 2026 | `/workspace/drive/living.txt` |
| `Tether.lean` (May 31; `projectionOrthogonalToU` was `sorry`) | May 31 2026, 1:32 AM CDT | https://drive.google.com/file/d/1vLWAfj2fA73OfdGvcDj1dx5PkiBwpoUS |

κ: κ = 1 was the May teaching placeholder; 3/2 came in Aug 26 2026. Here κ is free (Route A sets κ = S). History: `docs/timeline.md`, `docs/provenance_appendix.md`, `history/`.

## Build and count
`lake exe cache get && lake build && lake env lean scripts/Axioms.lean` (output in `axioms_output.txt`).

**Count method:** top-level declarations beginning with `theorem` or `lemma` in `TetherMayForm/*.lean`:
`grep -cE "^(private |protected )?(theorem|lemma) " TetherMayForm/*.lean`.
**137 theorems**, 0 `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`. (Earlier counts in commit messages, 96–127, used looser methods and are superseded.)

## License
Apache-2.0 (`LICENSE`), with `NOTICE`. Grok assisted; it is not an author.
