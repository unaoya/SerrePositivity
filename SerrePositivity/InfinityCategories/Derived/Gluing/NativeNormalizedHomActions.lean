module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.ActionYonedaInverse

/-! 実閉射で正規化した元 Hom の二射影は、元の gμ・νf の同じ Yoneda 像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "OX" => dgGluingCommaObject R C D M X
local notation "OY" => dgGluingCommaObject R C D M Y

lemma dgGluingNativeNormalizedHom_factor :
    dgGluingNativeNormalizedHom R C D M X Y =
      (dgGluingToComma R C D M).map X Y ≫
        dgGluingCommaNormalizedHom R D RM M.toFunctor OX OY := by
  rw [dgGluingNativeNormalizedHom, dgGluingNativeIdentityCommaFunctor_map,
    dgGluingCommaNormalizedHom, Category.assoc]
  rfl

lemma dgGluingNativeNormalizedHom_source :
    dgGluingNativeNormalizedHom R C D M X Y ≫
        dgFunctorCommaSourceHomMap R RM RM (DGFunctor.id RM)
          (dgGluingIdentityCommaObject R RM (representable R X.left))
          (dgGluingIdentityCommaObject R RM (M.rightAt Y.right)) =
      (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y) ≫
        (dgYonedaIso R X.left (M.rightAt Y.right)).inv := by
  change dgGluingNativeNormalizedHom R C D M X Y ≫
    dgFunctorCommaSourceHomMap R RM RM (DGFunctor.id RM)
      (dgGluingIdentityCommaObject R RM (dgGluingCommaObject R C D M X).replacement)
      (dgGluingIdentityCommaObject R RM (M.toFunctor.obj
        (dgGluingCommaObject R C D M Y).source)) = _
  rw [dgGluingNativeNormalizedHom_factor, Category.assoc,
    dgGluingCommaNormalizedHom_source R D RM M.toFunctor OX OY]
  change (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      (dgFunctorCommaSourceHomMap R D RM M.toFunctor OX OY ≫ M.toFunctor.map X.right Y.right) ≫
        eHomWhiskerRight (Complex R) (dgGluingAugmentation R C D M X)
          (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)) = _
  simp only [Category.assoc]
  rw [← Category.assoc (dgGluingHomRepresentableIso R C D M X Y).hom
      (dgFunctorCommaSourceHomMap R D RM M.toFunctor OX OY),
    dgGluingHomRepresentableIso_right]
  rw [dgGluingRightAction_yoneda_inverse R C D M X Y]

lemma dgGluingNativeNormalizedHom_replacement :
    dgGluingNativeNormalizedHom R C D M X Y ≫
        dgFunctorCommaReplacementHomMap R RM RM (DGFunctor.id RM)
          (dgGluingIdentityCommaObject R RM (representable R X.left))
          (dgGluingIdentityCommaObject R RM (M.rightAt Y.right)) =
      (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) ≫
        (dgYonedaIso R X.left (M.rightAt Y.right)).inv := by
  change dgGluingNativeNormalizedHom R C D M X Y ≫
    dgFunctorCommaReplacementHomMap R RM RM (DGFunctor.id RM)
      (dgGluingIdentityCommaObject R RM (dgGluingCommaObject R C D M X).replacement)
      (dgGluingIdentityCommaObject R RM (M.toFunctor.obj
        (dgGluingCommaObject R C D M Y).source)) = _
  rw [dgGluingNativeNormalizedHom_factor, Category.assoc,
    dgGluingCommaNormalizedHom_replacement R D RM M.toFunctor OX OY]
  change (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      dgFunctorCommaReplacementHomMap R D RM M.toFunctor OX OY ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
          (dgGluingAugmentation R C D M Y) = _
  rw [← Category.assoc (dgGluingHomRepresentableIso R C D M X Y).hom
      (dgFunctorCommaReplacementHomMap R D RM M.toFunctor OX OY),
    dgGluingHomRepresentableIso_left]
  simp only [Category.assoc]
  rw [dgGluingLeftAction_yoneda_inverse R C D M X Y]

end SerrePositivity.InfinityCategories
