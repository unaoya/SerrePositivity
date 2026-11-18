module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.RawAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionDifferential

/-!
模型。文献の定義との比較は後で
# 元の線形削除微分の同じ実基底での値

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のgeneratorとdifferentialを、同じrawComponentとcutSumで評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C284：元の生成元か零の評価を、同じcutSumか零として読む。 -/
lemma rawComponent_generator (S : SSet.{0}) {r d q : ℕ}
    (v : Fin ((r + 1) + d) → Fin (r + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v) (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective v ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v then
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S (⟨v, hv⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) x
      else 0 := by
  by_cases hv : Function.Surjective v ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v
  · rw [dite_eq_left hv]
    have hg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up (⟨v, hv⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d)) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A ⟨v, hv⟩
    rw [hg]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_value A S ⟨v, hv⟩ x
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator, dite_eq_right hv, map_zero, LinearMap.zero_apply]

/-- C285：元の線形削除微分を、同じ実基底と生成元で評価する。 -/
lemma rawComponent_differential_basis (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (r + 1) d
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
        (ModuleCat.freeMk (ULift.up x)) =
      ∑ i : Fin ((r + 1) + (d + 1)), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient w.val i •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val i))
          (ModuleCat.freeMk (ULift.up x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_basis]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord, map_sum, map_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
