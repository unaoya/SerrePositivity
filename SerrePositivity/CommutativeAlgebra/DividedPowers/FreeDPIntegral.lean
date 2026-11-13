module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPDerivation
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis

/-!
# 分冪偏微分の積分作用素

## 概要
自由分冪代数の各変数について、分冪単項式の指数を一つ上げる積分を定める。

## 方針
分冪単項式基底上で偏微分と積分を比較する。

## 規約
積分の定数項を零に取る。

## 使われ方
pd de Rham 列の Poincaré 補題。
-/

public noncomputable section

universe u v

open DividedPowerAlgebra Finset

namespace SerrePositivity.BhattScholze

variable {R : Type u} [CommRing R] {S : Type v}

local notation "D" => DividedPowerAlgebra R (S →₀ R)

private theorem freeDPPartial_factor (s t : S) (n : ℕ) (h : s ≠ t) :
    freeDPPartial s (dp R n (Finsupp.single t 1)) = 0 := by
  cases n with
  | zero => simp [dp_zero]
  | succ n => rw [freeDPPartial_dp_succ, Finsupp.single_eq_of_ne h, zero_smul]

private theorem partial_prod_without (s : S) (m : S →₀ ℕ) :
    freeDPPartial s (freeDPMonomial S R (m.erase s)) = 0 := by
  classical
  unfold freeDPMonomial Finsupp.prod
  let f (t : S) := dp R (m.erase s t) (Finsupp.single t (1 : R))
  have h (s' : Finset S) (h' : s ∉ s') : freeDPPartial s (∏ t ∈ s', f t) = 0 := by
    induction s' using Finset.induction_on with
    | empty => simp
    | insert t t' ht ih =>
      have hst : s ≠ t := fun h => h' (mem_insert.mpr (Or.inl h))
      rw [prod_insert ht, Derivation.leibniz, freeDPPartial_factor s t _ hst,
        ih (fun hs => h' (mem_insert_of_mem hs)), smul_zero, smul_zero, add_zero]
  exact h _ (by simp)

private theorem freeDPMonomial_split (s : S) (m : S →₀ ℕ) :
    dp R (m s) (Finsupp.single s 1) * freeDPMonomial S R (m.erase s) =
      freeDPMonomial S R m :=
  Finsupp.mul_prod_erase' m s (fun t n => dp R n (Finsupp.single t (1 : R)))
    (fun _ => dp_zero)

/-- 偏微分は指定座標の分冪の指数を一つ下げる。 -/
theorem freeDPPartial_monomial (s : S) (m : S →₀ ℕ) :
    freeDPPartial s (freeDPMonomial S R m) =
      if m s = 0 then 0 else freeDPMonomial S R (m - Finsupp.single s (1 : ℕ)) := by
  classical
  rw [← freeDPMonomial_split s m, Derivation.leibniz, partial_prod_without, smul_zero, zero_add]
  cases h : m s with
  | zero => simp [dp_zero]
  | succ n =>
    rw [ite_eq_right (Nat.succ_ne_zero n), freeDPPartial_dp_succ, Finsupp.single_eq_same,
      one_smul, smul_eq_mul, mul_comm]
    rw [← freeDPMonomial_split s (m - Finsupp.single s (1 : ℕ))]
    have h' : (m - Finsupp.single s (1 : ℕ)) s = n := by simp [h]
    have he : (m - Finsupp.single s (1 : ℕ)).erase s = m.erase s := by
      ext t
      by_cases ht : t = s
      · subst t
        simp
      · simp [Finsupp.erase_ne ht, Finsupp.single_eq_of_ne ht]
    rw [h', he]

/-- 分冪単項式の指定座標の指数を一つ上げる。 -/
def freeDPIntegral (s : S) : D →ₗ[R] D :=
  (freeDPBasis S R).constr R fun m => freeDPMonomial S R (m + Finsupp.single s (1 : ℕ))

/-- 積分作用素の基底上の値。 -/
@[simp]
theorem freeDPIntegral_monomial (s : S) (m : S →₀ ℕ) :
    freeDPIntegral s (freeDPMonomial S R m) = freeDPMonomial S R (m + Finsupp.single s (1 : ℕ)) := by
  rw [← freeDPBasis_apply]
  exact (freeDPBasis S R).constr_basis R _ _

/-- 分冪の積分を微分すると元に戻る。 -/
theorem freeDPPartial_integral (s : S) (x : D) :
    freeDPPartial s (freeDPIntegral s x) = x := by
  let f := (freeDPPartial (R := R) s).toLinearMap.comp (freeDPIntegral s)
  suffices h : f = LinearMap.id from DFunLike.congr_fun h x
  apply (freeDPBasis S R).ext
  intro m
  change freeDPPartial s (freeDPIntegral s (freeDPBasis S R m)) = freeDPBasis S R m
  rw [freeDPBasis_apply, freeDPIntegral_monomial, freeDPPartial_monomial]
  have h : (m + Finsupp.single s (1 : ℕ)) s ≠ 0 := by simp
  rw [ite_eq_right h, add_tsub_cancel_right]

/-- 指定座標で指数零の分冪単項式だけを残す射影。 -/
def freeDPConstantTerm (s : S) : D →ₗ[R] D :=
  (freeDPBasis S R).constr R fun m => if m s = 0 then freeDPMonomial S R m else 0

@[simp]
theorem freeDPConstantTerm_monomial (s : S) (m : S →₀ ℕ) :
    freeDPConstantTerm s (freeDPMonomial S R m) =
      if m s = 0 then freeDPMonomial S R m else 0 := by
  unfold freeDPConstantTerm
  conv_lhs => rw [← freeDPBasis_apply]
  rw [Module.Basis.constr_basis]

/-- 微分した後に積分すると、指定座標の定数項を除いた元を得る。 -/
theorem freeDPIntegral_partial (s : S) (x : D) :
    freeDPIntegral s (freeDPPartial s x) = x - freeDPConstantTerm s x := by
  let f := (freeDPIntegral (R := R) s).comp (freeDPPartial s).toLinearMap
  let g := LinearMap.id - freeDPConstantTerm (R := R) s
  suffices h : f = g from DFunLike.congr_fun h x
  apply (freeDPBasis S R).ext
  intro m
  change freeDPIntegral s (freeDPPartial s (freeDPBasis S R m)) =
    freeDPBasis S R m - freeDPConstantTerm s (freeDPBasis S R m)
  rw [freeDPBasis_apply, freeDPPartial_monomial, freeDPConstantTerm_monomial]
  by_cases h : m s = 0
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, sub_zero, freeDPIntegral_monomial]
    congr 1
    apply tsub_add_cancel_of_le
    intro t
    by_cases ht : s = t
    · subst t
      simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr h
    · simp [Finsupp.single_eq_of_ne (Ne.symm ht)]

/-- 異なる座標の積分と偏微分は可換。 -/
theorem freeDPPartial_integral_comm {s t : S} (h : s ≠ t) (x : D) :
    freeDPPartial s (freeDPIntegral t x) = freeDPIntegral t (freeDPPartial s x) := by
  let f := (freeDPPartial (R := R) s).toLinearMap.comp (freeDPIntegral t)
  let g := (freeDPIntegral (R := R) t).comp (freeDPPartial s).toLinearMap
  suffices e : f = g from DFunLike.congr_fun e x
  apply (freeDPBasis S R).ext
  intro m
  change freeDPPartial s (freeDPIntegral t (freeDPBasis S R m)) =
    freeDPIntegral t (freeDPPartial s (freeDPBasis S R m))
  rw [freeDPBasis_apply, freeDPIntegral_monomial, freeDPPartial_monomial, freeDPPartial_monomial,
    Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero]
  split_ifs
  · rw [map_zero]
  · rw [freeDPIntegral_monomial]
    congr 1
    ext a
    by_cases ha : a = s
    · subst a
      simp [Finsupp.single_eq_of_ne h]
    · simp [Finsupp.single_eq_of_ne ha]

end SerrePositivity.BhattScholze
