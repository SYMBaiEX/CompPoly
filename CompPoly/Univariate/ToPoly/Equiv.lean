/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import CompPoly.Univariate.ToPoly.Core

/-!
# `toPoly` Equivalence

Ring equivalences between computable univariate polynomials and `Polynomial`.
-/

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Semiring R] [BEq R]

section RingEquiv

-- `Raw.toPoly_neg`, `Raw.toPoly_sub`, `Raw.toPoly_mul`, `Raw.toPoly_C`, `Raw.toPoly_one`,
-- `Raw.toPoly_pow`, `Raw.toPoly_zero`, and `Raw.toPoly_X` were moved to
-- `CompPoly.Univariate.ToPoly.Raw` (below the `Raw.Proofs`/`Raw.Division` import cycle) so
-- that `Raw.Division` can use them. The `CPolynomial`-level wrappers below still delegate to
-- those `Raw.*` lemmas.

@[grind =]
lemma toPoly_neg {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (-p).toPoly = -p.toPoly := by
  exact Raw.toPoly_neg p.val

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  apply Raw.toPoly_add

@[grind =]
lemma toPoly_sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p + -q).toPoly = p.toPoly + -q.toPoly
  rw [toPoly_add, toPoly_neg]

@[grind =]
lemma Raw.toPoly_mul_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p * q).toPoly.coeff i = (p.toPoly * q.toPoly).coeff i := by
  rw [coeff_toPoly, mul_coeff, Polynomial.coeff_mul]; simp
  have h_antidiagonal :
      Finset.HasAntidiagonal.antidiagonal i =
      Finset.image (fun x => (x, i - x)) (Finset.range (i + 1)) := by
    exact Finset.Nat.antidiagonal_eq_image i
  simp [h_antidiagonal ]
  have h_coeff : ∀ x, p.toPoly.coeff x = p[x]?.getD 0 ∧ q.toPoly.coeff x = q[x]?.getD 0 := by
    intro x
    repeat rw [coeff_toPoly]
    constructor <;> simp
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases h_coeff x with ⟨hp, _hq⟩
  rcases h_coeff (i - x) with ⟨_, hq⟩
  simp [hp, hq]

@[grind =]
lemma toPoly_mul_coeffC [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p.val * q.val).toPoly.coeff i = (p.val.toPoly * q.val.toPoly).coeff i := by
  simpa using Raw.toPoly_mul_coeff p.val q.val i

@[grind =]
lemma toPoly_mul [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  exact Raw.toPoly_mul p.val q.val

@[simp, grind =]
lemma eval₂_C {R : Type*} [Semiring R] {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (r : R) :
    (Raw.C r).eval₂ f x = f r := by
  unfold CPolynomial.Raw.eval₂ Raw.C
  ring_nf
  simp [Array.zipIdx]

lemma toPoly_one [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).toPoly = 1 := by
  apply Raw.toPoly_one

lemma toPoly_zero {R : Type*} [Semiring R] : (0 : CPolynomial R).toPoly = 0 := by
  apply Raw.toPoly_zero

@[grind =]
lemma toPoly_pow [Nontrivial R] [LawfulBEq R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  change (p ^ n).val.toPoly = p.val.toPoly ^ n
  rw [val_pow]
  exact Raw.toPoly_pow p.val n

lemma toPoly_sum.{u} {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] {ι : Type u}
    [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∑ j ∈ s, f j).toPoly = ∑ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (toPoly_zero (R := R))
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, toPoly_add, ih]

lemma toPoly_prod.{u} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {ι : Type u} [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∏ j ∈ s, f j).toPoly = ∏ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [toPoly_one]
  | insert a s ha ih =>
      simp [Finset.prod_insert, ha, toPoly_mul, ih]

noncomputable def ringEquiv [LawfulBEq R] [Nontrivial R] :
  CPolynomial R ≃+* Polynomial R where
  toFun := CPolynomial.toPoly
  invFun := fun p => ⟨p.toImpl, isCanonical_toImpl p⟩
  left_inv := by
    unfold Function.LeftInverse; intro x
    apply Subtype.ext; apply toImpl_toPoly_of_canonical
  right_inv := by
    unfold Function.RightInverse CPolynomial.toPoly
    apply toPoly_toImpl
  map_mul' := by intros p q; rw [toPoly_mul p q]
  map_add' := by intros p q; apply toPoly_add

end RingEquiv

end CPolynomial

end CompPoly
