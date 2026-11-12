module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedIntervalEndpoints

/-!
概要：標準区間を元の持ち上げた区間へ移し、パラメーターと因子を交換する。
方針：二つの射影を組にして、自然性と始点を全射の等式で計算する。
規約：任意の大きいパラメーターを許す。使われ方：元の図式 comma の円柱の正規化。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 区間の正規化と、元の全パラメーターとの交換。 -/
def liftedIntervalFlip (T : SSet.{u + 1}) : T ⊗ (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⊗ T :=
  lift (snd T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall) (fst T Δ[1])

/-- この全形状比較は任意のパラメーター制限と厳密に可換。 -/
lemma liftedIntervalFlip_naturality {S T : SSet.{u + 1}} (f : S ⟶ T) :
    (f ▷ (Δ[1] : SSet.{u + 1})) ≫ liftedIntervalFlip T =
      liftedIntervalFlip S ≫ ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ◁ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 始点では、元の小さい区間の同じ始点での全評価になる。 -/
lemma liftedIntervalFlip_first (T : SSet.{u + 1}) :
    (T ◁ stdSimplex.δ 1) ≫ liftedIntervalFlip T =
      fst T (Δ[0] : SSet.{u + 1}) ≫
        lift (SSet.const (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))) (𝟙 T) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [liftedIntervalFlip, Category.assoc, lift_fst, SSet.comp_const]
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall_first, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramShapePoint, SSet.yonedaEquiv_symm_zero,
      SSet.comp_const]
  · simp only [liftedIntervalFlip, Category.assoc, lift_snd, Category.comp_id]
    exact whiskerLeft_fst _ _

/-- 正規化した全区間座標は元の同型の逆射。 -/
lemma liftedIntervalFlip_fst (T : SSet.{u + 1}) : liftedIntervalFlip T ≫
    fst ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u})) T =
      snd T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall := lift_fst _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
