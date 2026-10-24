module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeOriginalHomProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomInputFactor
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

lemma dgGluingNativeNormalizationHomInput_source_factor :
    dgGluingNativeNormalizationHomInput R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (pinchedHomChainMap ((dgFunctorCommaSource R RM RM (DGFunctor.id RM)).map IX IY)) =
      dgGluingNativeHomModelMap R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
        (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
          (homObject R D X.right Y.right)).hom ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingNativeRightCoefficientInput R C D M X Y) := by
  rw [dgGluingNativeNormalizationHomInput, dgGluingUniverseHomChainMap_post,
    dgGluingNativeIdentityCommaFunctor_original_source R C D M X Y]
  have h := dgGluingUniverseHomChainMap_input_factor.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} (C := DGGluingObject R C D M) (D := RM)
    (x := X) (y := Y) (x' := M.rightAt X.right) (y' := M.rightAt Y.right)
    (dgGluingRightHomMap R C D M X Y) (M.toFunctor.map X.right Y.right)
  simpa only [dgGluingNativeHomModelMap, dgGluingNativeRightCoefficientInput,
    dgGluingCommonComplexUniverse_hom_eq_hom] using h

lemma dgGluingNativeNormalizationHomInput_replacement_factor :
    dgGluingNativeNormalizationHomInput R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (pinchedHomChainMap ((dgFunctorCommaReplacement R RM RM (DGFunctor.id RM)).map IX IY)) =
      dgGluingNativeHomModelMap R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
        (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
          (homObject R C X.left Y.left)).hom ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingNativeLeftCoefficientInput R C D M X Y) := by
  rw [dgGluingNativeNormalizationHomInput, dgGluingUniverseHomChainMap_post,
    dgGluingNativeIdentityCommaFunctor_original_replacement R C D M X Y]
  have h := dgGluingUniverseHomChainMap_input_factor.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} (C := DGGluingObject R C D M) (D := RM)
    (x := X) (y := Y) (x' := representable R X.left) (y' := representable R Y.left)
    (dgGluingLeftHomMap R C D M X Y) (yonedaHom R C X.left Y.left)
  simpa only [dgGluingNativeHomModelMap, dgGluingNativeLeftCoefficientInput,
    dgGluingCommonComplexUniverse_hom_eq_hom] using h
end SerrePositivity.InfinityCategories
