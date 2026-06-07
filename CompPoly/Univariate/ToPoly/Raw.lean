/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles, Valerii Huhnin
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw.Ops

open Polynomial

/-- Convert a mathlib `Polynomial` to a `CPolynomial.Raw` by extracting coefficients
up to the degree. -/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomial.Raw R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => Array.ofFn (fun i : Fin (d + 1) => p.coeff i)

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
variable {Q : Type*} [Semiring Q] [BEq Q] [LawfulBEq Q]
variable {S : Type*} [Semiring S]

namespace Raw

/-
Helper: Horner foldr equals the naive sum-of-powers for lists.
-/
private lemma horner_eq_naive_list (f : R →+* S) (x : S) :
    ∀ (l : List R),
    l.foldr (fun a acc ↦ f a + acc * x) 0 =
    (l.zipIdx.map (fun ⟨a, i⟩ ↦ f a * x ^ i)).sum := by
  intro l
  induction' l using List.reverseRecOn with a l ih
  · rfl
  · simp +decide [*, List.zipIdx_append]
    rw [← ih]
    clear ih
    induction a <;> simp +decide [*, pow_succ, mul_assoc, add_mul, add_assoc]

/-
The default backend agrees with the naive sum-of-powers backend
(they share the same sum-of-powers fold definitionally).
-/
theorem eval₂_eq_eval₂_naive (f : R →+* S) (x : S) (p : CPolynomial.Raw R) :
    eval₂ f x p = eval₂Naive f x p := rfl

/-- Convert a `CPolynomial.Raw` to a (mathlib) `Polynomial`. -/
noncomputable def toPoly (p : CPolynomial.Raw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Evaluation is preserved by `toPoly`. -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial.Raw Q) : p.toPoly.eval x = p.eval x := by
  unfold toPoly Raw.eval
  rw [eval₂_eq_eval₂_naive, eval₂_eq_eval₂_naive]
  unfold eval₂Naive
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- The coefficients of `p.toPoly` match those of `p`. -/
lemma coeff_toPoly {p : CPolynomial.Raw Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
  unfold toPoly
  rw [eval₂_eq_eval₂_naive]
  unfold eval₂Naive

  let f := fun (acc: Q[X]) ((a,i): Q × ℕ) ↦ acc + Polynomial.C a * Polynomial.X ^ i
  change (Array.foldl f 0 p.zipIdx).coeff n = p.coeff n

  let motive (size: ℕ) (acc: Q[X]) := acc.coeff n = if (n < size) then p.coeff n else 0

  have zipIdx_size : p.zipIdx.size = p.size := by simp [Array.zipIdx]

  suffices h : motive p.zipIdx.size (Array.foldl f 0 p.zipIdx) by
    rw [h, ite_eq_left_iff, zipIdx_size]
    intro hn
    replace hn : n ≥ p.size := by linarith
    rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn, Option.getD_none]

  apply Array.foldl_induction motive
  · change motive 0 0
    simp [motive]

  change ∀ (i : Fin p.zipIdx.size) acc, motive i acc → motive (i + 1) (f acc p.zipIdx[i])
  unfold motive f
  intros i acc h
  have i_lt_p : i < p.size := by linarith [i.is_lt]
  have : p.zipIdx[i] = (p[i], ↑i) := by simp [Array.getElem_zipIdx]
  rw [this, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_X_pow, mul_ite, h]
  rcases (Nat.lt_trichotomy i n) with hlt | rfl | hgt
  · have h1 : ¬ (n < i) := by linarith
    have h2 : ¬ (n = i) := by linarith
    have h3 : ¬ (n < i + 1) := by linarith
    simp [h1, h2, h3]
  · simp [i_lt_p]
  · have h1 : ¬ (n = i) := by linarith
    have h2 : n < i + 1 := by linarith
    simp [hgt, h1, h2]

/-- Case analysis for `toImpl`: either the polynomial is zero or has a specific form. -/
lemma toImpl_elim (p : Q[X]) :
    (p = 0 ∧ p.toImpl = #[])
  ∨ (p ≠ 0 ∧ p.toImpl = Array.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
  unfold Polynomial.toImpl
  by_cases hbot : p.degree = ⊥
  · left
    use degree_eq_bot.mp hbot
    rw [hbot]
  right
  use degree_ne_bot.mp hbot
  have hnat : p.degree = p.natDegree := Polynomial.degree_eq_natDegree (degree_ne_bot.mp hbot)
  simp [hnat]

/-- `toImpl` is a right-inverse of `toPoly`: the round-trip from `Polynomial` is the identity.
  This shows `toPoly` is surjective and `toImpl` is injective. -/
theorem toPoly_toImpl {p : Q[X]} : p.toImpl.toPoly = p := by
  ext n
  rw [coeff_toPoly]
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨_, h⟩
  · simp [h]
  rw [h]
  by_cases h : n < p.natDegree + 1
  · simp [h]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, reduceDIte, Option.getD_none]
  replace h := Nat.lt_of_succ_le (not_lt.mp h)
  symm
  exact coeff_eq_zero_of_natDegree_lt h

/-- Trimming doesn't change the `toPoly` image. -/
@[grind =]
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial.Raw R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

private theorem matchSize_size_eq {p q : CPolynomial.Raw Q} :
    let (p', q') := Array.matchSize p q 0
    p'.size = q'.size := by
  change (Array.rightpad _ _ _).size = (Array.rightpad _ _ _).size
  rw [Array.size_rightpad, Array.size_rightpad]
  omega

private theorem matchSize_size {p q : CPolynomial.Raw Q} :
    let (p', _) := Array.matchSize p q 0
    p'.size = max p.size q.size := by
  change (Array.rightpad _ _ _).size = max (Array.size _) (Array.size _)
  rw [Array.size_rightpad]
  omega

private theorem zipWith_size {S : Type*} {f : S → S → S} {a b : Array S} (h : a.size = b.size) :
    (Array.zipWith f a b).size = a.size := by
  simp
  omega

private theorem addRaw_size {p q : CPolynomial.Raw Q} :
    (addRaw p q).size = max p.size q.size := by
  change (Array.zipWith _ _ _).size = max p.size q.size
  rw [zipWith_size matchSize_size_eq, matchSize_size]

private theorem addRaw_coeff (p q : CPolynomial.Raw Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  rcases Nat.lt_or_ge i (addRaw p q).size with hi | hi
  · have hget : (addRaw p q)[i] = p.coeff i + q.coeff i := by
      simp [addRaw]
      by_cases hp : i < p.size <;> by_cases hq : i < q.size <;> simp_all
    simpa [coeff, hi] using hget
  · have hmax : max p.size q.size ≤ i := by
      simpa [addRaw_size (p := p) (q := q)] using hi
    have hp : p.size ≤ i := le_trans (le_max_left _ _) hmax
    have hq : q.size ≤ i := le_trans (le_max_right _ _) hmax
    simp [coeff, hi, hp, hq]

/-- `toPoly` preserves addition. -/
@[grind =]
theorem toPoly_addRaw {p q : CPolynomial.Raw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, addRaw_coeff]

/-- `toPoly` of a right-scalar multiplication is multiplication by `Polynomial.C r` on the right. -/
@[grind =]
theorem toPoly_smulRight {p : CPolynomial.Raw Q} {r : Q} :
    (smulRight r p).toPoly = p.toPoly * Polynomial.C r := by
  ext n
  rw [Polynomial.coeff_mul_C, coeff_toPoly, coeff_toPoly]
  show (Array.map (fun a => a * r) p).getD n 0 = p.getD n 0 * r
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p[n]? with
  | none => simp
  | some a => simp

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  change (p.add q).toPoly = p.toPoly + q.toPoly; unfold add
  rw [toPoly_trim, toPoly_addRaw]

/-- Non-zero polynomials map to non-empty arrays. -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

/-- The last coefficient of `toImpl p` is the leading coefficient of `p`. -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

/-- `toImpl` lands in the semantic canonical carrier used by `CPolynomial`. -/
@[simp]
theorem isCanonical_toImpl (p : R[X]) : IsCanonical p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · simpa [h] using (Trim.isCanonical_empty (R := R))
  · intro hp
    have hlast : p.toImpl.getLast hp = p.leadingCoeff := by
      simpa using (getLast_toImpl (Q := R) (p := p) h_nz)
    rw [hlast]
    exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

/-- `toImpl` produces canonical polynomials (no trailing zeros). -/
@[simp, grind =]
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  exact Trim.trim_eq_of_isCanonical (isCanonical_toImpl p)

/-- The round-trip from `CPolynomial.Raw` to `Polynomial` and back yields the canonical form. -/
@[simp, grind =]
theorem Raw.toImpl_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) : p.toPoly.toImpl = p.trim := by
  have h_inj : ∀ a b : CPolynomial.Raw R, IsCanonical a → IsCanonical b → a.toPoly = b.toPoly → a = b := by
    intro a b ha hb hab
    apply Trim.canonical_ext (Trim.trim_eq_of_isCanonical ha) (Trim.trim_eq_of_isCanonical hb)
    intro i
    rw [← coeff_toPoly, hab, coeff_toPoly]
  have h_canonical_toImpl := isCanonical_toImpl p.toPoly
  have h_canonical_trim := Trim.isCanonical_trim p
  have h_eq : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
  have h_eq' : p.toPoly = p.trim.toPoly := by rw [toPoly_trim]
  have h_eq_both : p.toPoly.toImpl.toPoly = p.trim.toPoly := by rw [← h_eq, h_eq']
  exact h_inj _ _ h_canonical_toImpl h_canonical_trim h_eq_both

/-- Compatibility alias for the non-duplicated `CPolynomial.Raw` namespace. -/
@[simp, grind =]
theorem toImpl_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) : p.toPoly.toImpl = p.trim := by
  exact _root_.CompPoly.CPolynomial.Raw.Raw.toImpl_toPoly p

/-- A nonempty trimmed raw polynomial bounds the degree of its `toPoly` image. -/
theorem Raw.toPoly_natDegree_lt_trim_size_of_pos [LawfulBEq R]
    (p : CPolynomial.Raw R) (hp : 0 < p.trim.size) :
    p.toPoly.natDegree < p.trim.size := by
  have hround := Raw.toImpl_toPoly (R := R) p
  have hsize : p.toPoly.toImpl.size = p.trim.size := congrArg Array.size hround
  rcases toImpl_elim p.toPoly with ⟨_hzero, himpl⟩ | ⟨_hnz, himpl⟩
  · have : p.trim.size = 0 := by
      rw [← hsize, himpl]
      simp
    omega
  · have himpl_size : p.toPoly.toImpl.size = p.toPoly.natDegree + 1 := by
      simp [himpl]
    omega

/-- Compatibility alias for the non-duplicated `CPolynomial.Raw` namespace. -/
theorem toPoly_natDegree_lt_trim_size_of_pos [LawfulBEq R]
    (p : CPolynomial.Raw R) (hp : 0 < p.trim.size) :
    p.toPoly.natDegree < p.trim.size := by
  exact _root_.CompPoly.CPolynomial.Raw.Raw.toPoly_natDegree_lt_trim_size_of_pos p hp

/-- Evaluation is preserved by `toImpl`. -/
@[simp, grind =]
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), Raw.toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming. -/
@[simp, grind =]
lemma eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial.Raw R) :
    p.trim.eval x = p.eval x := by
  rw [← Raw.toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end Raw

end CPolynomial

end CompPoly
