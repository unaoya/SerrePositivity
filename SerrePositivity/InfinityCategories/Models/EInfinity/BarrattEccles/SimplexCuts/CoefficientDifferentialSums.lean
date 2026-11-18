module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundarySums

/-!
模型。文献の定義との比較は後で
# 元の線形係数微分と同じ全係数境界和

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のfinCongrで同じ削除位置を移し、元の線形微分の像へ全有限和をまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C297：同じ全係数境界和は、元の線形削除微分の像の負号。 -/
lemma sum_coefficientBoundaryTerm_succ (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r (d + 1) q,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r (d + 1) q w c x) =
      -((eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (r + 1) d
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
          (ModuleCat.freeMk (ULift.up x)))) := by
  have he : (r + 1) + (d + 1) = r + d + 2 := by omega
  have hr := (finCongr he).sum_comp
    (fun p : Fin (r + d + 2) => ∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r (d + 1) q w (p, s) x)
  rw [Fintype.sum_prod_type]
  trans ∑ i : Fin ((r + 1) + (d + 1)), ∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r (d + 1) q w (Fin.cast he i, s) x
  · convert hr.symm using 1
    all_goals rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_differential_basis A S w x]
    simp only [map_sum, map_zsmul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm_sum_cut A S w (Fin.cast he i) x h,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_generator_erase_positiveWord A S w i x]
    by_cases hv : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val (Fin.cast he i)) ∧
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val (Fin.cast he i))
    · simp only [dite_eq_left hv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletionCoefficient_positiveWord, neg_smul]
    · simp only [dite_eq_right hv, map_zero, smul_zero, neg_zero]

/-- C298：係数次数零の全係数境界和は、元の定義のまま零。 -/
lemma sum_coefficientBoundaryTerm_zero (S : SSet.{0}) {r q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) 0) (x : S _⦋q⦌) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r 0 q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r 0 q w c x) = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm, Finset.sum_const_zero]

/-- C299：入力次数零の全入力境界和は、元の定義のまま零。 -/
lemma sum_simplexBoundaryTerm_zero (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋0⦌) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexBoundaryIndex r d 0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S w 0 c x) = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm, Finset.sum_const_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
