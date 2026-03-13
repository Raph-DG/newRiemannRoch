import Mathlib
import newRiemannRoch.Mathlib.AlgebraicCycle.ExactSequence

/-!
# Euler characteristics

This file is mainly meant to signal the intended direction of the
project - significant amounts of work are being sorried out.

That said, this hopefully gives some impression of what we eventually
aim to prove.

Currently I'm being a little bit cavalier with the assumptions made on
things. I'm doing this for a couple of reasons. For one, it's easier, and
also it's unclear to me right now precisely what form these assumptions
should take.

TODO: Flesh out the definitions in this file more, even just for demonstration
purposes
-/

open AlgebraicGeometry CategoryTheory AlgebraicCycle Sheaf

universe u

variable {X : Scheme.{u}}

def χ (F : X.Modules) : ℤ := sorry

lemma χ_additive (c : ShortComplex X.Modules) (hc : c.Exact) :
  χ c.X₂ = χ c.X₁ + χ c.X₃ := sorry

lemma χ_skyscraper (p : X)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    χ (skyscraperSheafOfModules p) = 1 := sorry

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

lemma riemann_roch (D : AlgebraicCycle X ℤ) : χ (D.sheafOfModules) = sorry := sorry
