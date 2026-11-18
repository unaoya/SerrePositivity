module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorBoundaryTerms

/-!
模型。文献の定義との比較は後で
# 同じ斉次純粋テンソルの因子ごとの微分

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の任意の二複体の微分公式を、tensorValueと同じ右括弧に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 既存のテンソル微分の各因子の成分を、同じ右括弧で評価した略記。 -/
def tensorValueDifferentialFactor (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (∀ i, K.X (-(d i : ℤ))) → Fin n → (power K n).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ) + 1)
  | 0, _, _, i => Fin.elim0 i
  | n + 1, d, v, i => Fin.cases
      (ιTensorObj K (power K n) (-(d 0 : ℤ) + 1)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun j => d j.succ) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ) + 1)
        (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add]; omega)
        (K.d (-(d 0 : ℤ)) (-(d 0 : ℤ) + 1) (v 0) ⊗ₜ[A]
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n (fun j => d j.succ) (fun j => v j.succ)))
      (fun j => (-(d 0 : ℤ)).negOnePow •
        ιTensorObj K (power K n) (-(d 0 : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun k => d k.succ) : ℤ) + 1)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ) + 1)
          (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add]; omega)
          (v 0 ⊗ₜ[A] tensorValueDifferentialFactor K n
            (fun k => d k.succ) (fun k => v k.succ) j)) i

/-- C259：任意の同じ純粋テンソルの微分は、各因子の微分の和。 -/
lemma tensorValue_d_sum (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
    (v : ∀ i, K.X (-(d i : ℤ))) :
    (power K n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v) = ∑ i : Fin n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor K n d v i := by
  induction n with
  | zero =>
    change ((HomologicalComplex.single (ModuleCat A) (.up ℤ) 0).obj
      (𝟙_ (ModuleCat A))).d 0 1 _ = _
    rw [single_obj_d]
    simp
  | succ n ih =>
    change (K ⊗ power K n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ))
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K (n + 1) d v) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorPair_d_apply, ih]
    simp only [Fin.sum_univ_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor, Fin.cases_zero, Fin.cases_succ,
      TensorProduct.tmul_sum, map_sum, Finset.smul_sum]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
