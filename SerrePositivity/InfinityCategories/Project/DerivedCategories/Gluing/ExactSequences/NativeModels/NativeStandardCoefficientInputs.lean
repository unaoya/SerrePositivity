module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.NativeOriginalHomProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeNormalizationCubes
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.NativeCoefficientActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.UniverseTransport.UniverseHomInputFactor
/-! # native 標準合成面の正本係数入力への因子分解

概要：標準面の左右可変入力を元 Hom の鎖射影と正本係数入力へ同定する。
方針：native 関手の二射影と、一般宇宙の Hom 模型の因子分解を合成する。
規約：元の全入力と同じ augmentation を保持する。
使われ方：単位補正の標準係数端を三角形全体で正本へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "RM" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y

lemma dgGluingNativeNormalizationHomInput_source_factor :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R RM RM (DGFunctor.id RM)).map IX IY)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
          (_root_.SerrePositivity.DifferentialGraded.homObject R D X.right Y.right)).hom ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor_original_source R C D M X Y]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_input_factor.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (D := RM)
    (x := X) (y := Y) (x' := M.rightAt X.right) (y' := M.rightAt Y.right)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y) (M.toFunctor.map X.right Y.right)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexUniverse_hom_eq_hom] using h

lemma dgGluingNativeNormalizationHomInput_replacement_factor :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R RM RM (DGFunctor.id RM)).map IX IY)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
          (_root_.SerrePositivity.DifferentialGraded.homObject R C X.left Y.left)).hom ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor_original_replacement R C D M X Y]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_input_factor.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (D := RM)
    (x := X) (y := Y) (x' := _root_.SerrePositivity.DifferentialGraded.representable R X.left) (y' := _root_.SerrePositivity.DifferentialGraded.representable R Y.left)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) (yonedaHom R C X.left Y.left)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexUniverse_hom_eq_hom] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
