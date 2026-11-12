module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarIntervalTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCollarDiagonalEvaluation
/-! # 正本導来四面体からの実補正対角の写像空間三角形

概要：左右の実補正対角を、正本導来写像空間の同じ二単体の指定面として保持する。
方針：四面体全体の再添字を端点固定で curry する。
規約：二つの補正対角・元 Hom 入力・全時間を変更しない。
使われ方：実補正道の対角合成を、高次貼り合わせと選択済み変形の相対比較へ供給する。
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

def dgGluingNativeUnitCollarIntervalTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarIntervalTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily_two_interval R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily_zero_interval R C D M X Y)

lemma dgGluingNativeUnitCollarIntervalTriangle_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingNativeUnitCollarIntervalTriangle R C D M X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarIntervalTriangle_evaluate _ _ _ _ _

lemma dgGluingNativeUnitCollarIntervalTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCollarIntervalTriangle R C D M X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarIntervalTriangle_two _ _ _ _ _

lemma dgGluingNativeUnitCollarIntervalTriangle_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCollarIntervalTriangle R C D M X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarIntervalTriangle_zero _ _ _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
