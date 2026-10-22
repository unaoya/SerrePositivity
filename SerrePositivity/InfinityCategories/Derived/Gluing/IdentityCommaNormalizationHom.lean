module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationClosed

/-! 恒等 comma 内の実標準閉射による、全 Hom 複体の正規化前合成・後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))

def dgGluingIdentityCommaPreNormalizeHom :
    dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement) Y :=
  (λ_ _).inv ≫ (dgGluingIdentityCommaNormalizationIn R E X ▷ _) ≫
    dgFunctorCommaComposition R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E X.replacement) X Y

def dgGluingIdentityCommaPostNormalizeHom :
    dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E) X
        (dgGluingIdentityCommaObject R E Y.source) :=
  (ρ_ _).inv ≫ (_ ◁ dgGluingIdentityCommaNormalizationOut R E Y) ≫
    dgFunctorCommaComposition R E E (DGFunctor.id E) X Y
      (dgGluingIdentityCommaObject R E Y.source)

lemma dgGluingIdentityCommaPreNormalizeHom_closed :
    dgGluingIdentityCommaPreNormalizeHom R E X Y =
      eHomWhiskerRight (Complex R) (dgGluingIdentityCommaNormalizationClosedIn R E X)
        (ForgetEnrichment.of (Complex R) Y) := rfl

lemma dgGluingIdentityCommaPostNormalizeHom_closed :
    dgGluingIdentityCommaPostNormalizeHom R E X Y =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X)
        (dgGluingIdentityCommaNormalizationClosedOut R E Y) := rfl

end SerrePositivity.InfinityCategories
