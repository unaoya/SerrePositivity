module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaObject

/-! 恒等 comma の任意対象間の比較差を、同じ二射の実 augmentation による前後合成へ展開する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  (K : Complex R) (a : K ⟶ homObject R E X.source Y.source)
  (b : K ⟶ homObject R E X.replacement Y.replacement)

lemma dgGluingIdentityCommaGeneralDifference_lift :
    biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E) X Y =
      (show K ⟶ homObject R E X.replacement Y.source from
        a ≫ eHomWhiskerRight (Complex R) X.augmentation
          (ForgetEnrichment.of (Complex R) Y.source)) -
      (show K ⟶ homObject R E X.replacement Y.source from
        b ≫ eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Y.augmentation) := by
  let p : homObject R E X.source Y.source ⟶ homObject R E X.replacement Y.source :=
    eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source)
  let q : homObject R E X.replacement Y.replacement ⟶ homObject R E X.replacement Y.source :=
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_lift_difference a b p q
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, DGFunctor.id, EnrichedFunctor.id]
  simp only [Category.id_comp]
  convert h using 1
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
