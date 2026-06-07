/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles, Tomaz Mascarenhas
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Raw.Core
import CompPoly.Univariate.Raw.Division

/-!
  # Polynomial Division

  This file defines computable univariate polynomial
  division, and proves an equivalence with Mathlib's
  polynomial division.
-/
namespace CompPoly

open CPolynomial

section MonicDivision

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
abbrev divByMonic (p q : CPolynomial R) : CPolynomial R :=
  p.divByMonic q

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
abbrev modByMonic (p q : CPolynomial R) : CPolynomial R :=
  p.modByMonic q

end MonicDivision

section Division

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- Remainder of `p` modulo a monic polynomial `q`, using a remainder-only implementation. -/
abbrev modByMonicRemainderOnly (p q : CPolynomial R) : CPolynomial R :=
  p.modByMonicRemainderOnly q

/-- Remainder of `p` modulo a monic polynomial `q`, using reversal and low products. -/
abbrev modByMonicByReversal (M : Raw.MulLowContext R) (p q : CPolynomial R) : CPolynomial R :=
  p.modByMonicByReversal M q

/-- The remainder-only monic remainder agrees with the canonical monic remainder. -/
theorem modByMonicRemainderOnly_eq_modByMonic (p q : CPolynomial R) :
    modByMonicRemainderOnly p q = modByMonic p q := by
  exact CPolynomial.modByMonicRemainderOnly_eq_modByMonic p q

/-- Quotient of `p` by `q` (when `R` is a field). -/
abbrev div (p q : CPolynomial R) : CPolynomial R :=
  p.div q

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
abbrev mod (p q : CPolynomial R) : CPolynomial R :=
  p.mod q

instance : Div (CPolynomial R) := ⟨div⟩
instance : Mod (CPolynomial R) := ⟨mod⟩

/-- Normalize a nonzero polynomial to monic form. The zero polynomial stays zero. -/
abbrev monicNormalize (p : CPolynomial R) : CPolynomial R :=
  CPolynomial.ofArray (Raw.monicNormalize p.val)

/-- Euclidean gcd with explicit fuel, normalized to a monic result. -/
abbrev gcdMonicWithFuel (fuel : Nat) (p q : CPolynomial R) : CPolynomial R :=
  CPolynomial.ofArray (Raw.gcdMonicWithFuel fuel p.val q.val)

/-- Monic Euclidean gcd for canonical univariate polynomials. -/
abbrev gcdMonic (p q : CPolynomial R) : CPolynomial R :=
  CPolynomial.ofArray (Raw.gcdMonic p.val q.val)

end Division

-- Re-export the field-level monic-normalization and gcd wrappers into the
-- `CPolynomial` namespace, where the correctness theorems and downstream callers
-- (`Roots/`, `NTTFast/`) reference them.
namespace CPolynomial
export CompPoly (monicNormalize gcdMonicWithFuel gcdMonic)
end CPolynomial

end CompPoly
