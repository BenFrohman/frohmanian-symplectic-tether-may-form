# Publication note: provenance of the Riccati / cubic-absorption comparison ODE

**Author of the mathematical content:** Benjamin Stanley Frohman (git identities "Benjamin Stanley Frohman", "Frohmanian", "BenFrohman").
**Scope:** This note covers only provenance. It is not a claim about the Clay Millennium Problem. Everything formalized here concerns a scalar ODE comparison or the *tethered* system. It says nothing about plain Navier–Stokes.
**Excluded:** I did not use any material by Félix Robles.

## 1. Method
- I searched 64 bare mirrors of the author's GitHub repositories, full history (`git log --all -G`, `git grep`), plus this repo's `history/` folder.
- For each source the note gives the commit hash and the commit date (box timezone CDT, UTC−05:00). It also gives the SHA-256 of the file blob at that commit (`git show H:path | sha256sum`) and the matching lines, quoted verbatim.
- Reproduce with: `git --git-dir=<repo> show <hash>:<path> | sha256sum`.

## 2. Sources, earliest first

### 2a. Earliest *self-dated* content (2026-05-18 and 2026-05-21)
These texts carry their own May 2026 dates. Their copies in this repo were committed on 2026-10-29. Git therefore proves the content existed only from the 2026-06-19 mirror onward (§2b). The May dates come from the documents themselves.

| Date in text | File (repo: tether-may-form) | commit | sha256 | verbatim |
|---|---|---|---|---|
| 2026-05-18 | history/2026-05-18_roadmap/roadmap_excerpt.txt:12 | 03a314d3eb0c6cb7aa532c5b90422322e28c74dc | 945d1b201f0e980dcf2479a1e244997294fc38461488d789d6637b00991b9c58 | "The global regularity of the system is governed by the following Riccati inequality, which provides a uniform, first-principles bound on vorticity: $$\|\omega(t)\|_{L^\infty} \le \sqrt{C}\tanh(\sqrt{C}t+\phi_0)$$" |
| 2026-05-21 | history/2026-05-21_PASS2_C3/Full_Living_PASS2_excerpt.md:1,55,57 | 7fe28288ce844cf6d533f382c8d0d7f34a6be12a | bef2b37c517067b6157203f515e1a2838c69f26ac56e23a3c2e9116634499236 | "## PASS 2 — Section 2.7 Canonicity Expansion + Riccati & Jacobi Clarification (2026-05-21)" · "y' = C y^2 - \kappa'' y^3" · "The cubic term arises naturally from the quartic absorption and yields a stronger uniform bound than the pure Riccati envelope." |
| 2026-05-21 | history/2026-05-21_vFinal_audit_email/grok_audit_0521.txt:121 | f2fd3ed070d69e9e8ea52351b1fd2a42663c1d1f | f12e7014f36ea472f74897a1cb03ac7cb5d3e92b881fdc72b796fa4dc83a52df | "The comparison principle then gives M(t) ≤ max(M(0), y_*) uniformly." |

### 2b. Earliest *git-timestamped* source: 2026-06-19 16:29:21 CDT
Repo **NS_Millennium_Proof**, commit `236244dc70379e2b26205da1d7867c0efe9ed1fd` ("Initial commit of Frohmanian Symplectic Tether NS Millennium Proof"), author Benjamin Stanley Frohman. The same tree appears in Test-Practice-Repo at `c4fc018`.

| path @ commit | sha256 | verbatim |
|---|---|---|
| historical/docs/Full_Living_Document_NS_Millennium_Proof.md @ c4fc01899f36 | 384270d1e4411d4546b569f963068b7d30f0dd60f51138e2e26f09629749c824 | l.220 "y' = C y^2 - \kappa'' y^3, \qquad y(0) = M_\varepsilon(0)," · l.443 "## PASS 2 — … Riccati & Jacobi Clarification (2026-05-21)" · l.497 "y' = C y^2 - \kappa'' y^3" · l.555 "f(y) := C y^2 - \kappa'' y^3 = y^2 (C - \kappa'' y)" |
| NS_Millennium_Proof/Modules/TetheredLyapunov.lean @ 236244d | ba9d2df26bef454c0aa2d74fa3ebd88626aafa554fa7c491329a0dd547ae5e04 | l.706 "y' = C y² − κ'' y³,    y(0) = y0" · l.832 "Equilibria: solve C y² − κ'' y³ = 0 ⇒ y² (C − κ'' y) = 0 ⇒ y = 0 or y* = C/κ''." |
| Modules/IndependentMajorant.lean @ 236244d | 4bd4cb3a1f87e568293e4a28bcf401c00cc16e23215b301ec2ac1b4cff980d18 | l.26 "y' = C y² - κ'' y³ , y(0) = M_ε(0)" |
| Blueprint.md @ 236244d | 25643cec13ffa383132aafc1c1ec79cb9e30a4aa61bd2dbaf7a6e7caa18f7225 | l.594 "Independent comparison majorant ODE y' = C y² − κ'' y³ (completely decoupled from NS)." |

### 2c. Later sources
- Clay- `1f69807bf4087e7c1949f4bcafb585554bf16636` (2026-10-07 10:03:32 CDT, "Frohmanian"): lean/Clay/Gaps/ConditionalRiccati.lean, sha256 f534b5cc8ab27c2fa96586ed1fedb73d11947a9bf88659207e37adf45b3ca900. It contains `theorem conditional_riccati (hRiccati : CorrectedMaxRate)`. This is a conditional statement, and its hypothesis is left open.
- symplectohydronamics ec00857 (2026-08-22) and frohmanian-symplectic-tether-regularity e0a5667 (2026-10-25) restate the same comparison ODE.

## 3. Side by side with this repo (tether-may-form)

| Author's original (date) | tether-may-form Lean | companion.tex |
|---|---|---|
| y' = C y² − κ'' y³ (PASS 2, 2026-05-21; git 2026-06-19) | `Layer2.comparisonField C κ'' y = C*y^2 - κ''*y^3` | §Layer 2 and §Riccati provenance |
| equilibria 0, y* = C/κ'' ; M ≤ max(M(0), y*) | `Layer2.comparison_bound`, `Riccati.tethered_ceiling` | §Riccati provenance |
| pure Riccati envelope √C tanh(√C t+φ0) (2026-05-18) vs. cubic is "stronger" | `Riccati.ricSol`, `ricSol_hasDerivAt`, `riccati_blowup` (plain y' = C y² has explicit blow-up at T* = 1/(C y0)) | §Riccati provenance |
| quartic absorption → cubic damping | `EnstrophyL2.enstrophy_deriv_logistic`, `tethered_enstrophy_uniform` (E ≤ max(E0, C²/(2κ²))) | ll. 227–235 |
| log-loss variant | `LogLoss.logThreshold`, `comparison_bound_logloss` | ll. 258–262 |

**What is new in tether-may-form:** the L² enstrophy form E' ≤ (C²/κ)E − 2κE² and its cap C²/(2κ²). I found no earlier copy of these in the mirrors. Its earliest commit is in this repo, 91e229a (2026-10-29 21:39 CDT). What it builds on is the author's cubic-absorption comparison principle from May/June 2026.

## 4. What is machine-checked
- The plain Riccati equation y' = C y² with C, y0 > 0 has the explicit solution y0/(1 − C y0 t), which exceeds every bound before T* = 1/(C y0) (`riccati_blowup`).
- Under the tethered comparison y' ≤ C y² − κ'' y³ with κ'' > 0, y ≤ max(y(0), C/κ'') for all time (`tethered_ceiling`).
- Both are scalar ODE facts. Neither says anything about the regularity of plain 3-D Navier–Stokes.

## 5. Addendum: the 4/3 exponent comes from interpolation
In this repo the exponent 4/3 is an interpolation and Young exponent. It is not a bracket coefficient. It enters at the H¹ rung: Gagliardo–Nirenberg/Sobolev gives N ≤ A G^{1/4} L^{3/2}, and then Young's inequality is applied with exponents (4, 4/3) (`PalinstrophyH1.lean`, companion.tex §Result 2). The author's May 2026 chain already uses Gagliardo–Nirenberg interpolation: "M_ε(t) ≤ C_GN ‖ω_ε‖_{L⁶}^{3/2} ‖ω_ε‖_{L²}^{1/2} + …" (Full_Living_Document @ c4fc018). The field-level bracket coefficients are 3/2 and 3i/8 (`FieldJacobi.lean`). See companion.tex §Metriplectic.
