module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleUniversalLongHom

/-!
概要：元の L の全 K・全区間の普遍族は、高次単体も区別する。
方針：普遍区間を二度 curry すると、元の fiber 包含と内部 Hom の同型の合成になる。
規約：K の頂点への制限だけではこの単射性を適用しない。
使われ方：実 encoder の厳密切断に残る、全 K 区間族の回収条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全 K の普遍区間族は、元の長 Hom 空間を単射に表示する。 -/
instance controlledTriangleUniversalInterval_curry_mono (X Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    Mono (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval X Z K c)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalLongHom
  rw [curry_natural_right, curry_uncurry]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
