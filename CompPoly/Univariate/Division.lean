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

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.modByMonic p.val q.val)⟩

end MonicDivision

section Division

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- Remainder of `p` modulo a monic polynomial `q`, using a remainder-only implementation. -/
def modByMonicRemainderOnly (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonicRemainderOnly p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.modByMonicRemainderOnly p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`, using reversal and low products. -/
def modByMonicByReversal (M : Raw.MulLowContext R) (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonicByReversal M p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.modByMonicByReversal M p.val q.val)⟩

/-- The remainder-only monic remainder agrees with the canonical monic remainder. -/
theorem modByMonicRemainderOnly_eq_modByMonic (p q : CPolynomial R) :
    modByMonicRemainderOnly p q = modByMonic p q := by
  apply CPolynomial.ext
  simp [modByMonicRemainderOnly, modByMonic, Raw.modByMonicRemainderOnly_eq_modByMonic]

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.mod p.val q.val)⟩

instance : Div (CPolynomial R) := ⟨div⟩
instance : Mod (CPolynomial R) := ⟨mod⟩

/-- Equality between `div` and `divByMonic` for `CPolynomial R`. -/
theorem div_eq_divByMonic (p q : CPolynomial R) :
    div p q =
      divByMonic (q.leadingCoeff⁻¹ • p) (q.leadingCoeff⁻¹ • q) := by
  apply Subtype.ext
  show (Raw.div p.val q.val).trim = _
  apply congrArg Raw.trim
  show Raw.div p.val q.val = _
  have hq_lc : Raw.leadingCoeff q.val = q.leadingCoeff :=
    show q.val.trim.getLastD 0 = q.val.getLastD 0 by rw [CPolynomial.trim_eq q]
  rw [Raw.div, hq_lc, smul_eq_mul, Raw.C_mul_eq_smul_trim, Raw.C_mul_eq_smul_trim]
  rfl

/-- Equality between `mod` and `modByMonic` for `CPolynomial R`. -/
theorem mod_eq_modByMonic (p q : CPolynomial R) :
    mod p q =
      modByMonic p (q.leadingCoeff⁻¹ • q) := by
  apply Subtype.ext
  show (Raw.mod p.val q.val).trim = _
  apply congrArg Raw.trim
  show Raw.mod p.val q.val = _
  have hq_lc : Raw.leadingCoeff q.val = q.leadingCoeff := by
    show q.val.trim.getLastD 0 = q.val.getLastD 0
    rw [CPolynomial.trim_eq q]
  rw [Raw.mod, hq_lc]
  change Raw.modByMonic p.val (Raw.C q.leadingCoeff⁻¹ * q.val) =
    Raw.modByMonic p.val ((Raw.smul q.leadingCoeff⁻¹ q.val).trim)
  rw [Raw.C_mul_eq_smul_trim]

/-- Any `CPolynomial` divided by the zero polynomial gives the zero
polynomial. -/
@[simp]
theorem div_zero (p : CPolynomial R) : div p 0 = 0 := by
  apply Subtype.ext; show (Raw.div p.val 0).trim = 0; unfold Raw.div
  rw [Raw.mul_zero, Raw.leadingCoeff_zero, inv_zero]
  rw [smul_eq_mul, Raw.C_mul_eq_smul_trim, Raw.smul_zero_trim]
  change (0 : CPolynomial.Raw R).trim = 0
  exact Raw.Trim.canonical_empty

/-- Normalize a nonzero polynomial to monic form. The zero polynomial stays zero. -/
def monicNormalize (p : CPolynomial R) : CPolynomial R :=
  CPolynomial.ofArray (Raw.monicNormalize p.val)

/-- Euclidean gcd with explicit fuel, normalized to a monic result. -/
def gcdMonicWithFuel :
    Nat → CPolynomial R → CPolynomial R → CPolynomial R
  | fuel, p, q => CPolynomial.ofArray (Raw.gcdMonicWithFuel fuel p.val q.val)

/-- Monic Euclidean gcd for canonical univariate polynomials. -/
def gcdMonic (p q : CPolynomial R) : CPolynomial R :=
  CPolynomial.ofArray (Raw.gcdMonic p.val q.val)

end Division
