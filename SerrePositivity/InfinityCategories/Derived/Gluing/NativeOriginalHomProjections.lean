module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityComma
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections
/-! # native comma 比較の元左右 Hom 射影

概要：native 関手の二射影を、元 gluing Hom の左右鎖射影へ厳密に戻す。
方針：comma image の射影自然性と Hom 模型同型の二射影を使う。
規約：元複体と二つの鎖射影を変更しない。
使われ方：補正標準面を正本係数三角形へ全入力で同定する。
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
local notation "OX" => dgGluingCommaObject R C D M X
local notation "OY" => dgGluingCommaObject R C D M Y
lemma dgGluingNativeIdentityCommaFunctor_original_source :
    (dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
      (dgFunctorCommaSource R RM RM (DGFunctor.id RM)).map IX IY =
      dgGluingRightHomMap R C D M X Y ≫ M.toFunctor.map X.right Y.right := by
  rw [dgGluingNativeIdentityCommaFunctor_map, Category.assoc]
  change (dgGluingToComma R C D M).map X Y ≫
    (dgGluingCommaImageHomMap R D RM M.toFunctor OX OY ≫
      dgFunctorCommaSourceHomMap R RM RM (DGFunctor.id RM) IX IY) = _
  erw [dgGluingCommaImageHomMap_source R D RM M.toFunctor OX OY]
  change (dgGluingHomRepresentableIso R C D M X Y).hom ≫
    (dgFunctorCommaSourceHomMap R D RM M.toFunctor OX OY ≫
      M.toFunctor.map X.right Y.right) = _
  erw [← Category.assoc, dgGluingHomRepresentableIso_right R C D M X Y]
lemma dgGluingNativeIdentityCommaFunctor_original_replacement :
    (dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
      (dgFunctorCommaReplacement R RM RM (DGFunctor.id RM)).map IX IY =
      dgGluingLeftHomMap R C D M X Y ≫ yonedaHom R C X.left Y.left := by
  rw [dgGluingNativeIdentityCommaFunctor_map, Category.assoc]
  change (dgGluingToComma R C D M).map X Y ≫
    (dgGluingCommaImageHomMap R D RM M.toFunctor OX OY ≫
      dgFunctorCommaReplacementHomMap R RM RM (DGFunctor.id RM) IX IY) = _
  erw [dgGluingCommaImageHomMap_replacement R D RM M.toFunctor OX OY]
  exact dgGluingHomRepresentableIso_left R C D M X Y
end SerrePositivity.InfinityCategories
