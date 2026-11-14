module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NativeUnitCollarDiagonalTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeUnitCompositionInputPaths
/-! # 四面体の補正対角三角形と実入力対角道

概要：対角三角形の二面を、元入力 fiber 内の実補正道の対角評価へ厳密に同定する。
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

lemma dgGluingNativePreCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_two_interval :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily_two R C D M X Y,
    dgGluingNativePreCollarInputPath_diagonal_evaluation R C D M X Y]

lemma dgGluingNativeExitCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_zero_interval :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily_zero R C D M X Y,
    dgGluingNativeExitCollarInputPath_diagonal_evaluation R C D M X Y]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
