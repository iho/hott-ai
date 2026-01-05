# hott-ai

Minimal Agda playground for experimenting with Martin-Lof Type Theory (MLTT) in the context of Homotopy Type Theory (HoTT).

## Layout

- `hott-ai.agda-lib` — Agda library file pointing the Agda compiler to `src` and the standard library dependency.
- `src/MLTT/Universe.agda` — simple wrappers around Agda universes with Type, Type0, Type1, Type2 helpers and a `levelJoin` alias.
- `src/MLTT/PiSigma.agda` — basic Pi (dependent function) and Sigma (dependent pair) formers with projection helpers.
- `src/MLTT/Identity.agda` — identity type with the J eliminator, transport, symmetry, transitivity, and congruence lemmas.

## Using the code

1. Install Agda and the standard library that ships with it.
2. Open the project with `agda --library-file hott-ai.agda-lib` or configure your editor to load the `.agda-lib` file.
3. Import the MLTT modules from an interactive Agda buffer:
   ```agda
   open import MLTT.Universe
   open import MLTT.PiSigma
   open import MLTT.Identity
   ```
4. Start defining additional type formers (natural numbers, universes, higher inductive types) by following the roadmap in `plan.md`.

The current code is intentionally lightweight to make it easy to extend while studying the constructions outlined in `plan.md`.
