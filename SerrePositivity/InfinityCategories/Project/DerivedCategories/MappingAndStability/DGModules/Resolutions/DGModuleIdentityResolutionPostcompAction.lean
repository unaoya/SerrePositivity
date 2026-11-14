module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleIdentityResolutionPostcompHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionUnitComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.EnrichedCochainClosed
/-!
概要：入力を変更する実分解射との合成を、三成分すべてで厳密に回収する。
方針：実射影と比較 cochain の二項を単位挿入から計算する。
規約：全 Hom 複体・全次数の式。使われ方：分解変更の厳密自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)))
  (M : RightModule R E)
  (a : ForgetEnrichment.of (Complex R) Y.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)

def dgModuleIdentityResolutionPostcompAction :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) :=
  ((ρ_ _).inv ≫ _ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_source :
    dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.source) a := by
  rw [dgModuleIdentityResolutionPostcompAction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_source]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceComposite]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_postcompose (Complex R)
    (ForgetEnrichment (Complex R) (RightModule R E)) _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ _ a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_source R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_replacement :
    dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y := by
  rw [dgModuleIdentityResolutionPostcompAction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_replacement]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementComposite]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_rightUnit (Complex R) (RightModule R E) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_replacement R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_firstPrimitive :
    (Cochain.ofHom ((ρ_ _).inv ≫
      _ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement.val) a)) (add_zero (-1)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
        ForgetEnrichment.homTo (Complex R) a := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_source, EnrichedFunctor.id_map, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_postcompose (ForgetEnrichment (Complex R) (RightModule R E))
    _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ a hi (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y)

lemma dgModuleIdentityResolutionPostcompAction_secondPrimitive :
    (Cochain.ofHom ((ρ_ _).inv ≫
      _ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) Y
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_comparison R E Y M a hs hq
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_leftTensor_zero _ _ _ hz, Cochain.zero_comp]

lemma dgModuleIdentityResolutionPostcompAction_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) _
      (dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement.val) a)) (add_zero (-1)) := by
  rw [dgModuleIdentityResolutionPostcompAction,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleIdentityResolutionPostcompAction_firstPrimitive,
    dgModuleIdentityResolutionPostcompAction_secondPrimitive, add_zero]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
