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

section Division

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.modByMonic p.val q.val)⟩

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

/-- Any `CPolynomial` divided by the zero polynomial gives the zero
polynomial. -/
@[simp]
theorem div_zero (p : CPolynomial R) : p.div 0 = 0 := by
  apply Subtype.ext; show (Raw.div p.val 0).trim = 0; unfold Raw.div
  rw [Raw.mul_zero, Raw.leadingCoeff_zero, inv_zero]
  rw [smul_eq_mul, Raw.C_mul_eq_smul_trim, Raw.smul_zero_trim]; rfl

/-- Any `CPolynomial` modulo the zero polynomial gives the zero
polynomial. -/
@[simp]
theorem mod_zero (p : CPolynomial R) : p.mod 0 = 0 := by
  apply Subtype.ext; show (Raw.mod p.val 0).trim = 0; unfold Raw.mod
  rw [Raw.mul_zero, Raw.leadingCoeff_zero, inv_zero]
  rw [smul_eq_mul, Raw.C_mul_eq_smul_trim, Raw.smul_zero_trim]; rfl

end Division

section ImplementationCorrectness

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- `div` matches `Polynomial.div` with respect to `toPoly` -/
theorem div_toPoly (p q : CPolynomial R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  show (Raw.div p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  exact Raw.div_toPoly p.val q.val

/-- `mod` matches `Polynomial.mod` with respect to `toPoly` -/
theorem mod_toPoly (p q : CPolynomial R) (hq : q ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  show (Raw.mod p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  have hq_val : q.val.toPoly ≠ 0 := by
    intro h
    apply hq
    apply CPolynomial.ext
    have hsize := (Raw.trim_size_zero_iff_toPoly_zero q.val).mpr h
    simp_all only [ne_eq, trim_eq, Array.size_eq_zero_iff, Array.empty_eq]
    rfl
  exact Raw.mod_toPoly p.val q.val hq_val

end ImplementationCorrectness
