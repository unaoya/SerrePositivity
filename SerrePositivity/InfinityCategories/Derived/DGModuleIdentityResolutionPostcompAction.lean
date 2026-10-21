module
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPostcompHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionUnitComparison
public import SerrePositivity.InfinityCategories.Derived.EnrichedCochainClosed
/-!
概要：入力を変更する実分解射との合成を、三成分すべてで厳密に回収する。
方針：実射影と比較 cochain の二項を単位挿入から計算する。
規約：全 Hom 複体・全次数の式。使われ方：分解変更の厳密自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (X Y : DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)))
  (M : RightModule R E)
  (a : ForgetEnrichment.of (Complex R) Y.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)

def dgModuleIdentityResolutionPostcompAction :
    dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y ⟶
    dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) :=
  ((ρ_ _).inv ≫ _ ◁ dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) ≫
    dgModuleFunctorResolutionComposition R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y
      (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_source :
    dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq ≫
      dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
    dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.source) a := by
  rw [dgModuleIdentityResolutionPostcompAction, Category.assoc,
    dgModuleFunctorResolutionComposition_source]
  dsimp only [dgModuleFunctorResolutionSourceComposite]
  exact parameterEnriched_postcompose (Complex R)
    (ForgetEnrichment (Complex R) (RightModule R E)) _ _ _
    (dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ _ a
    (dgModuleIdentityResolutionPostcompHom_source R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_replacement :
    dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq ≫
      dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
    dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y := by
  rw [dgModuleIdentityResolutionPostcompAction, Category.assoc,
    dgModuleFunctorResolutionComposition_replacement]
  dsimp only [dgModuleFunctorResolutionReplacementComposite]
  exact parameterEnriched_rightUnit (Complex R) (RightModule R E) _ _
    (dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ _
    (dgModuleIdentityResolutionPostcompHom_replacement R E Y M a hs hq)

lemma dgModuleIdentityResolutionPostcompAction_firstPrimitive :
    (Cochain.ofHom ((ρ_ _).inv ≫
      _ ◁ dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) =
    (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement.val) a)) (add_zero (-1)) := by
  have hi : dgModuleIdentityResolutionPostcompHom R E Y M a hs hq ≫
      dgModuleFunctorResolutionImageHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) Y
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) =
        ForgetEnrichment.homTo (Complex R) a := by
    rw [dgModuleFunctorResolutionImageHomMap, ← Category.assoc,
      dgModuleIdentityResolutionPostcompHom_source, EnrichedFunctor.id_map, Category.comp_id]
  exact enrichedCochain_postcompose (ForgetEnrichment (Complex R) (RightModule R E))
    _ _ _ (dgModuleIdentityResolutionPostcompHom R E Y M a hs hq) _ a hi (-1)
    (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y)

lemma dgModuleIdentityResolutionPostcompAction_secondPrimitive :
    (Cochain.ofHom ((ρ_ _).inv ≫
      _ ◁ dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) = 0 := by
  rw [dgModuleFunctorResolutionSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom
      (dgModuleIdentityResolutionPostcompHom R E Y M a hs hq)).comp
      (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) Y
        (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq)) (zero_add (-1)) = 0 :=
    dgModuleIdentityResolutionPostcompHom_comparison R E Y M a hs hq
  rw [complexRightUnitInsertion_leftTensor_zero _ _ _ hz, Cochain.zero_comp]

lemma dgModuleIdentityResolutionPostcompAction_comparison :
    dgModuleFunctorResolutionHomComparison R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E Y M a hs hq) _
      (dgModuleIdentityResolutionPostcompAction R E X Y M a hs hq) =
    (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement.val) a)) (add_zero (-1)) := by
  rw [dgModuleIdentityResolutionPostcompAction,
    dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionComposition_comparison,
    dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleIdentityResolutionPostcompAction_firstPrimitive,
    dgModuleIdentityResolutionPostcompAction_secondPrimitive, add_zero]
end
end SerrePositivity.InfinityCategories
