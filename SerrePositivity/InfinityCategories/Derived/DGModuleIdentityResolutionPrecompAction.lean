module
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPostcompHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionUnitComparison
public import SerrePositivity.InfinityCategories.Derived.EnrichedParameterizedClosed
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
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)

def dgModuleIdentityResolutionPrecompAction :
    dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y ⟶
    dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y :=
  ((λ_ _).inv ≫ dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _) ≫
    dgModuleFunctorResolutionComposition R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y

lemma dgModuleIdentityResolutionPrecompAction_source :
    dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq ≫
      dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y =
    dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y ≫
        eHomWhiskerRight (Complex R) a (ForgetEnrichment.of (Complex R) Y.source) := by
  rw [dgModuleIdentityResolutionPrecompAction, Category.assoc,
    dgModuleFunctorResolutionComposition_source]
  dsimp only [dgModuleFunctorResolutionSourceComposite]
  exact parameterEnriched_precompose (Complex R)
    (ForgetEnrichment (Complex R) (RightModule R E)) _ _ _
    (dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _ _ a
    (dgModuleIdentityResolutionPostcompHom_source R E X M a hs hq)

lemma dgModuleIdentityResolutionPrecompAction_replacement :
    dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq ≫
      dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y =
    dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  rw [dgModuleIdentityResolutionPrecompAction, Category.assoc,
    dgModuleFunctorResolutionComposition_replacement]
  dsimp only [dgModuleFunctorResolutionReplacementComposite]
  exact parameterEnriched_leftUnit (Complex R) (RightModule R E) _ _
    (dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _ _
    (dgModuleIdentityResolutionPostcompHom_replacement R E X M a hs hq)

lemma dgModuleIdentityResolutionPrecompAction_firstPrimitive :
    (Cochain.ofHom ((λ_ _).inv ≫
      dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y) (zero_add (-1)) = 0 := by
  rw [dgModuleFunctorResolutionFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom
      (dgModuleIdentityResolutionPostcompHom R E X M a hs hq)).comp
      (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E X M a hs hq)) (zero_add (-1)) = 0 :=
    dgModuleIdentityResolutionPostcompHom_comparison R E X M a hs hq
  rw [complexLeftUnitInsertion_rightTensor_zero _ _ _ hz, Cochain.zero_comp]

lemma dgModuleIdentityResolutionPrecompAction_secondPrimitive :
    (Cochain.ofHom ((λ_ _).inv ≫
      dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y) (zero_add (-1)) =
    dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  exact enrichedCochain_leftUnit (RightModule R E) _ _
    (dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _
    (dgModuleIdentityResolutionPostcompHom_replacement R E X M a hs hq) (-1)
    (dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y)

lemma dgModuleIdentityResolutionPrecompAction_comparison :
    dgModuleFunctorResolutionHomComparison R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y _
      (dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq) =
    dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  rw [dgModuleIdentityResolutionPrecompAction,
    dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionComposition_comparison,
    dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleIdentityResolutionPrecompAction_firstPrimitive,
    dgModuleIdentityResolutionPrecompAction_secondPrimitive, zero_add]
end
end SerrePositivity.InfinityCategories
