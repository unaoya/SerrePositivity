module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomDerivedInputPathEquivalence
/-! # 元入力を持つ導来対角 path 引き戻しの Kan 性

概要：左右入力を保持する導来合成対角の path 引き戻しは Kan 複体である。
方針：既存の二入力 fiber の Kan 性と区間両端射影の Kan 性を適用する。
規約：元入力を忘れず、モデル構造の instance を仮定しない。
使われ方：同じ既知の実逆射を正本入力付き比較へ輸送して往復ホモトピーを合成する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
lemma dgGluingDerivedCompositionInputPathPullback_kanComplex :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback R C D M X Y) := by
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber] at hl hf ht
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
