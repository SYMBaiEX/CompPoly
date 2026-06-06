/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Linear
import CompPoly.Univariate.ToPoly.Raw

open Polynomial

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

/-- Convert a `CPolynomial` to a (mathlib) `Polynomial`. -/
noncomputable def toPoly [Zero R] [Semiring R] (p : CPolynomial R) : Polynomial R := p.val.toPoly

/-- `ofArray` preserves the raw polynomial's `toPoly` image. -/
theorem ofArray_toPoly [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    (CPolynomial.ofArray p).toPoly = p.toPoly := by
  unfold CPolynomial.ofArray
  exact Raw.toPoly_trim

/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomial R` to `Polynomial R`. -/
@[grind =]
lemma toImpl_toPoly_of_canonical [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p := by
  suffices h_inj : ∀ q : CPolynomial R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [Raw.toPoly_toImpl]
    exact
      h_inj ⟨p.toPoly.toImpl, Raw.isCanonical_toImpl p.toPoly⟩ this
        |> congrArg Subtype.val
        |>.symm
  intro q hpq
  apply CPolynomial.ext
  apply Raw.Trim.isCanonical_ext p.property q.property
  intro i
  rw [← Raw.coeff_toPoly, ← Raw.coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)

/-- `toPoly` maps a canonical polynomial to `0` iff the polynomial is `0`. -/
theorem toPoly_eq_zero_iff [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.toPoly = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply CPolynomial.ext
    calc
      (p : CPolynomial.Raw R) = p.toPoly.toImpl := (toImpl_toPoly_of_canonical p).symm
      _ = (0 : CPolynomial.Raw R) := by
        simp [hp, Polynomial.toImpl]
  · rintro rfl
    ext n
    rw [CPolynomial.toPoly, Raw.coeff_toPoly, Polynomial.coeff_zero]
    simpa [CPolynomial.coeff] using (CPolynomial.coeff_zero (R := R) n)

end CPolynomial

end CompPoly
