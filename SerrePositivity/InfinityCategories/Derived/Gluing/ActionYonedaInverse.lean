module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ActionYoneda

/-! 同じ二作用を、元の augmentation との実加群 Hom 合成として回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLeftAction_yoneda_inverse (X Y : DGGluingObject R C D M) :
    dgGluingLeftAction R C D M X Y ≫ (dgYonedaIso R X.left (M.rightAt Y.right)).inv =
      yonedaHom R C X.left Y.left ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
          (dgGluingAugmentation R C D M Y) := by
  rw [← dgGluingLeftAction_yoneda R C D M X Y]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma dgGluingRightAction_yoneda_inverse (X Y : DGGluingObject R C D M) :
    dgGluingRightAction R C D M X Y ≫ (dgYonedaIso R X.left (M.rightAt Y.right)).inv =
      M.toFunctor.map X.right Y.right ≫
        eHomWhiskerRight (Complex R) (dgGluingAugmentation R C D M X)
          (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)) := by
  rw [← dgGluingRightAction_yoneda R C D M X Y]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
