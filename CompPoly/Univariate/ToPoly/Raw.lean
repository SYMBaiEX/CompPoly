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
omit [BEq R] [LawfulBEq R] in
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
The Horner backend agrees with the naive sum-of-powers backend.
-/
omit [BEq R] [LawfulBEq R] in
theorem eval₂_eq_eval₂_naive (f : R →+* S) (x : S) (p : CPolynomial.Raw R) :
    eval₂ f x p = eval₂Naive f x p := by
  convert horner_eq_naive_list f x p.toList using 1
  · unfold eval₂
    aesop
  · unfold CPolynomial.Raw.eval₂Naive
    induction p using Array.recOn
    simp +decide [*]
    induction ‹List R› using List.reverseRecOn <;>
      simp +decide [*, List.zipIdx_append]

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

omit [BEq Q] [LawfulBEq Q] in
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

/-- Coefficientwise behaviour of `addRaw`.

  Provenance: this mirrors `CompPoly.CPolynomial.Raw.add_coeff?` from
  `CompPoly/Univariate/Raw/Proofs.lean`, re-proved locally because that module
  transitively imports `ToPoly.Raw` (via `Raw.Division`), so importing it here would
  create a cycle. Kept private to avoid colliding with the public `add_coeff?`. -/
private theorem addRaw_coeff_eq (p q : CPolynomial.Raw Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  have h_size : (addRaw p q).size = max p.size q.size := by
    change (Array.zipWith _ _ _).size = max p.size q.size
    simp only [addRaw, Array.size_zipWith, Array.size_rightpad]
    omega
  rcases Nat.lt_or_ge i (addRaw p q).size with h_lt | h_ge
  · have h_pad : ∀ (a b : CPolynomial.Raw Q) (h : i < (a.rightpad b.size 0).size),
        (a.rightpad b.size 0)[i] = a.coeff i := by
      intro a b h
      simp only [Array.rightpad, coeff, Array.getD_eq_getD_getElem?, Array.getElem_append]
      split
      · rw [Array.getElem?_eq_getElem (by assumption), Option.getD_some]
      · rw [Array.getElem_replicate, Array.getElem?_eq_none (by omega), Option.getD_none]
    have h_get : (addRaw p q)[i]'h_lt = p.coeff i + q.coeff i := by
      show (Array.zipWith (· + ·) (p.rightpad q.size 0) (q.rightpad p.size 0))[i]'h_lt
        = p.coeff i + q.coeff i
      rw [Array.getElem_zipWith, h_pad p q, h_pad q p]
    rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h_lt, Option.getD_some, h_get]
  · rw [h_size] at h_ge
    have h_p : i ≥ p.size := le_of_max_le_left h_ge
    have h_q : i ≥ q.size := le_of_max_le_right h_ge
    have h_lt' : i ≥ (addRaw p q).size := by rw [h_size]; exact h_ge
    rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_lt', Option.getD_none,
      coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_p, Option.getD_none,
      coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_q, Option.getD_none, add_zero]

/-- `toPoly` preserves addition. -/
@[grind =]
theorem toPoly_addRaw {p q : CPolynomial.Raw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, addRaw_coeff_eq]

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

/-! ### Constant, variable, zero, one, multiplication, and negation bridges

These bridge lemmas duplicate ones in `CompPoly/Univariate/ToPoly/Equiv.lean`, but are
re-proved here (below the `Raw.Proofs`/`Raw.Division` import cycle) so that
`Raw.Division` — which transitively imports this module but cannot import `Proofs`
or `Equiv` without creating a cycle — has them in scope. -/

/-- `toPoly` of the constant polynomial. -/
@[simp]
theorem toPoly_C {R : Type*} [Semiring R] (r : R) : (Raw.C r).toPoly = Polynomial.C r := by
  unfold toPoly Raw.C CPolynomial.Raw.eval₂
  simp [Array.foldr]

/-- `toPoly` of the zero polynomial. -/
@[simp]
theorem toPoly_zero {R : Type*} [Semiring R] : (0 : CPolynomial.Raw R).toPoly = 0 := by
  show (Raw.mk #[] : CPolynomial.Raw R).toPoly = 0
  unfold toPoly CPolynomial.Raw.eval₂
  simp [Array.foldr]

/-- `toPoly` of the one polynomial. -/
@[simp]
theorem toPoly_one {R : Type*} [Semiring R] : (1 : CPolynomial.Raw R).toPoly = 1 := by
  show (Raw.C (1 : R)).toPoly = 1
  rw [toPoly_C, map_one]

/-- `toPoly` of the variable `X`. -/
@[simp]
theorem toPoly_X {R : Type*} [Semiring R] : (Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X := by
  unfold toPoly Raw.X CPolynomial.Raw.eval₂
  simp [Array.foldr]

/-- Coefficientwise behaviour of negation. Mirrors `CompPoly.CPolynomial.Raw.neg_coeff`
  from `Raw.Proofs` (re-proved here to avoid the import cycle). -/
theorem neg_coeff {R : Type*} [NegZeroClass R] (p : CPolynomial.Raw R) (i : ℕ) :
    p.neg.coeff i = - p.coeff i := by
  unfold neg coeff
  rcases Nat.lt_or_ge i p.size with hi | hi <;> simp [hi]

/-- `toPoly` respects negation. -/
@[grind =]
theorem toPoly_neg {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    (-p).toPoly = -p.toPoly := by
  ext i
  rw [Polynomial.coeff_neg, coeff_toPoly, coeff_toPoly]
  change p.neg.coeff i = -p.coeff i
  exact neg_coeff p i

/-- `toPoly` of a left-scalar multiplication is multiplication by `Polynomial.C r` on the left. -/
theorem toPoly_smul {p : CPolynomial.Raw Q} {r : Q} :
    (smul r p).toPoly = Polynomial.C r * p.toPoly := by
  ext n
  rw [Polynomial.coeff_C_mul, coeff_toPoly, coeff_toPoly]
  show (Array.map (fun a => r * a) p).getD n 0 = r * p.getD n 0
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p[n]? with
  | none => simp
  | some a => simp

/-- Coefficientwise behaviour of multiplication by `X^i` (a coefficient shift). -/
theorem mulPowX_coeff (p : CPolynomial.Raw Q) (i n : ℕ) :
    (p.mulPowX i).coeff n = if i ≤ n then p.coeff (n - i) else 0 := by
  unfold mulPowX coeff
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_replicate,
    Array.getElem?_replicate]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- `toPoly` of multiplication by `X^i` (a coefficient shift). -/
theorem toPoly_mulPowX {p : CPolynomial.Raw Q} {i : ℕ} :
    (p.mulPowX i).toPoly = p.toPoly * Polynomial.X ^ i := by
  ext n
  rw [Polynomial.coeff_mul_X_pow', coeff_toPoly, coeff_toPoly, mulPowX_coeff]

/-- Coefficients vanish beyond the stored size. -/
theorem coeff_eq_zero_of_size_le {p : CPolynomial.Raw Q} {k : ℕ} (h : p.size ≤ k) :
    p.coeff k = 0 := by
  rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h, Option.getD_none]

/-- `toPoly` expressed as a finite sum of monomials over the stored coefficients. -/
theorem toPoly_eq_sum (p : CPolynomial.Raw Q) :
    p.toPoly = ∑ j ∈ Finset.range p.size, Polynomial.C (p.coeff j) * Polynomial.X ^ j := by
  ext k
  rw [coeff_toPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range p.size) k (fun j => p.coeff j)]
  by_cases hk : k < p.size
  · simp [hk]
  · simp only [Finset.mem_range, hk, if_false]
    exact coeff_eq_zero_of_size_le (Nat.not_lt.mp hk)

/-- `toPoly` of the untrimmed multiplication accumulator respects multiplication. -/
theorem toPoly_mulRaw (p q : CPolynomial.Raw Q) :
    (mulRaw p q).toPoly = p.toPoly * q.toPoly := by
  rw [toPoly_eq_sum p, Finset.sum_mul]
  have hsize : p.zipIdx.size = p.size := by simp
  have key : (mulRaw p q).toPoly =
      ∑ j ∈ Finset.range p.zipIdx.size,
        Polynomial.C (p.coeff j) * Polynomial.X ^ j * q.toPoly := by
    unfold mulRaw
    refine Array.foldl_induction
      (motive := fun n (acc : CPolynomial.Raw Q) => acc.toPoly =
        ∑ j ∈ Finset.range n, Polynomial.C (p.coeff j) * Polynomial.X ^ j * q.toPoly)
      ?_ ?_
    · simp only [Finset.range_zero, Finset.sum_empty]
      show (Raw.mk #[] : CPolynomial.Raw Q).toPoly = 0
      exact toPoly_zero
    · intro j acc ih
      have hzip : p.zipIdx[j] = (p[j.val]'(by simpa using j.isLt), j.val) := by
        simp [Array.getElem_zipIdx]
      rw [Finset.sum_range_succ, ← ih, hzip, toPoly_addRaw, toPoly_mulPowX, toPoly_smul]
      have hcoeff : p.coeff j.val = p[j.val]'(by simpa using j.isLt) := by
        rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using j.isLt),
          Option.getD_some]
      rw [hcoeff, mul_assoc, mul_assoc, (Polynomial.X_pow_mul (n := j) (p := q.toPoly))]
  rw [key, hsize]

/-- `toPoly` respects multiplication. -/
@[grind =]
theorem toPoly_mul [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  change (p.mul q).toPoly = p.toPoly * q.toPoly
  unfold mul
  rw [toPoly_trim, toPoly_mulRaw]

/-- `toPoly` respects subtraction. -/
@[grind =]
theorem toPoly_sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p + -q).toPoly = p.toPoly + -q.toPoly
  rw [toPoly_add, toPoly_neg]

/-- `toPoly` respects exponentiation by naturals. -/
@[grind =]
theorem toPoly_pow [LawfulBEq R] (p : CPolynomial.Raw R) : ∀ n : ℕ,
    (p ^ n).toPoly = p.toPoly ^ n
  | 0 => by
    show ((1 : CPolynomial.Raw R)).toPoly = _
    simp [toPoly_one]
  | n + 1 => by
    have hstep : (p ^ (n + 1)) = p * (p ^ n) := by
      show (mul p)^[n + 1] (Raw.C 1) = p.mul ((mul p)^[n] (Raw.C 1))
      rw [Function.iterate_succ_apply']
    rw [hstep, toPoly_mul, toPoly_pow p n, pow_succ']

omit [BEq Q] [LawfulBEq Q] in
/-- Non-zero polynomials map to non-empty arrays. -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

omit [BEq Q] [LawfulBEq Q] in
/-- The last coefficient of `toImpl p` is the leading coefficient of `p`. -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

omit [BEq R] in
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
    refine Trim.isCanonical_ext ha hb ?_
    intro i
    rw [← coeff_toPoly, hab, coeff_toPoly]
  have h_canonical_toImpl := isCanonical_toImpl p.toPoly
  have h_canonical_trim := Trim.isCanonical_trim p
  have h_eq : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
  have h_eq' : p.toPoly = p.trim.toPoly := by rw [toPoly_trim]
  have h_eq_both : p.toPoly.toImpl.toPoly = p.trim.toPoly := by rw [← h_eq, h_eq']
  exact h_inj _ _ h_canonical_toImpl h_canonical_trim h_eq_both

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

/-- Evaluation is preserved by `toImpl`. -/
@[simp, grind =]
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), Raw.toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming. -/
@[simp, grind =]
lemma Raw.eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial.Raw R) :
    p.trim.eval x = p.eval x := by
  rw [← Raw.toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end Raw

end CPolynomial

end CompPoly
