module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaNormalizationClosed

/-! 恒等 comma 内の実標準閉射による、全 Hom 複体の正規化前合成・後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))

def dgGluingIdentityCommaPreNormalizeHom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) Y :=
  (λ_ _).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X ▷ _) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement) X Y

def dgGluingIdentityCommaPostNormalizeHom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source) :=
  (ρ_ _).inv ≫ (_ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E Y) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E) X Y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source)

lemma dgGluingIdentityCommaPreNormalizeHom_closed :
    dgGluingIdentityCommaPreNormalizeHom R E X Y =
      eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)
        (ForgetEnrichment.of (Complex R) Y) := rfl

lemma dgGluingIdentityCommaPostNormalizeHom_closed :
    dgGluingIdentityCommaPostNormalizeHom R E X Y =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
