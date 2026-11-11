module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCompositionInputPaths
/-! # 単位補正対角と実入力対角道

概要：二つの単位補正の対角を、元入力 fiber 内の実補正道の対角評価へ厳密に同定する。
方針：同じ三角形評価の対角と区間 uncurry の自然性を使う。
規約：全時間と元 Hom 入力を保持する。
使われ方：四面体の高次貼り合わせを写像空間内の合成三角形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y


lemma dgGluingNativePreCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingNativeExitCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
