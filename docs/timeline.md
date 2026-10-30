# Timeline (America/Chicago; server timestamps converted from UTC)

| Date | Event | Evidence | Verified? |
|---|---|---|---|
| **May 2 2026, 7:28 PM CDT** | `main (3).tex` ("main3"): Frohman Triple Regularization Framework; 𝔗_F posed as a *conjecture* | Drive `main (3).tex` modifiedTime 2026-05-03T00:28:46Z (size 23130 = `main3_May03.tex`). The file itself says `\date{April 2026}` | Yes (Drive). Authorship may predate this (text says April) |
| May 16 2026, 5:52 PM CDT | `main (3).pdf` compiled copy | Drive modifiedTime 2026-05-16T22:52Z | Yes |
| **May 18 2026** | Living Draft v1 (10:29 AM CDT); Strategic Roadmap, Triple Regularization ("Negative Quadratic Feedback; matching fixed at κ=1"), 3:01 PM CDT | Drive modifiedTimes 15:29Z / 20:01Z | Yes. **"May 15" not verified**: no source found dated May 15 |
| **May 21 2026, 9:37 AM CDT** | vFinal PDF created (TF, projected kernel Π_u, degeneracy) | PDF CreationDate. (Drive copy re-modified Jun 26) | Yes |
| May 21 2026 | Grok AI audit ("referee report"; asks for Degeneracy Verification Lemma) | In-file `Date: 2026-05-21` only | Partially (internal date only) |
| **May 21 2026, 4:58 PM CDT** | Email to ai_eng@spacex.com with 3 photos (κ = 1, tanh bound) | Gmail sent 2026-05-21T21:58:21Z | Yes |
| May 23–24 2026 | Main8DRAFTAppends_v3.md (May 23 8:13 PM); Full Living Document md (May 24 11:42 AM) | Drive | Yes |
| May 27 2026, 4:30 PM CDT | vFinal.tex last edit | Drive | Yes |
| May 29 2026 | SymplecticTether.lean (5:36 PM); Formalization Roadmap (5:24 PM) | Drive | Yes |
| **May 30–31 2026** | Proof_Completeness_Report (May 30 10:51 PM), Triple.lean (11:09 PM), **Tether.lean (May 31 1:32 AM)**: C1–C3, `projectionOrthogonalToU := sorry`, C3 = `True` | Drive | Yes |
| Jun 26 2026 | Living FINAL Clay v1 / v1.1 docx last modified (source of the (A1)–(A5) and "negative quadratic feedback … fixed by matching" wording quoted here) | Drive | Yes — **but the A5 wording is only provably as old as Jun 26**; it matches the May 18 roadmap wording |
| **Aug 26 2026, 10:37 PM CDT** | Old repo (ns_push `2e6a407`/`7397212`): uniqueness closed via **saturation** hypothesis `SaturatesTetherQuadratic`; κ = 3/2 introduced | git commit dates (-0500) | Yes |
| **Oct 29 2026** | This reconstruction (`tether-may-form`), local only | git | Yes |

## Additions (Oct 29 2026 build)
- **2026-05-20** — "Route A" slide (screenshot, undated by server): C3 = negative feedback at
  |ω| maxima + 5-step + 9-term Jacobi on the reduced orbit (D→C→A→B). → `RouteAFeedback`.
- **2026-05-21** — PASS 2 §2.7 (C1)–(C3) wording, κ fixed by matching the stretching
  coefficient (Full_Living md, Drive modified 2026-05-24). → `matches_stretching`.
- **2026-06** — build_context Layer-2 rules (screenshot). → `Layer2.lean`.
- **2026-10-29** — Benjamin: symmetric and antisymmetric parts are orthogonal / invisible to
  each other (metriplectic). → `Metriplectic.lean`.

## Server-dated sources cited for the Route A build (America/Chicago, CDT)
- May 2 2026, 7:58 PM — NV_recovery2.pdf
- May 14 2026 — Frohmanian_Tether_Theorem.pdf; Leg 1 formality PDF
- May 15–16 2026 — Triple conjecture PDFs
- May 18 2026 — Strategic Roadmap docs
- May 20 2026, 12:16 AM — Drive PDF `1hof-GCX1M1hjKM3hw20jYRvevM6hu035`: (A5) feedback at maxima; quartic weight forced by uniqueness
- May 20 2026, 8:10 PM — v2.2 Master .tex (κ > 4C″)
- May 21 2026 — AI audit by Grok (not a human referee)
- May 24 2026 — Full_Living document
- May 27 2026 — vFinal.tex
- May 30–31 2026 — Tether.lean
- Oct 29 2026 — `Main.lean` (κ derived by Route A matching) and `Jacobi.lean` (9-term expansion)
