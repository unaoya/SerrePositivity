module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleIdentityResolutionPostcompHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionUnitComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedParameterizedClosed
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
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)

def dgModuleIdentityResolutionPrecompAction :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y :=
  ((λ_ _).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y

lemma dgModuleIdentityResolutionPrecompAction_source :
    dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y ≫
        eHomWhiskerRight (Complex R) a (ForgetEnrichment.of (Complex R) Y.source) := by
  rw [dgModuleIdentityResolutionPrecompAction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_source]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceComposite]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_precompose (Complex R)
    (ForgetEnrichment (Complex R) (RightModule R E)) _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _ _ a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_source R E X M a hs hq)

lemma dgModuleIdentityResolutionPrecompAction_replacement :
    dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  rw [dgModuleIdentityResolutionPrecompAction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_replacement]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementComposite]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_leftUnit (Complex R) (RightModule R E) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_replacement R E X M a hs hq)

lemma dgModuleIdentityResolutionPrecompAction_firstPrimitive :
    (Cochain.ofHom ((λ_ _).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq)) (zero_add (-1)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_comparison R E X M a hs hq
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftUnitInsertion_rightTensor_zero _ _ _ hz, Cochain.zero_comp]

lemma dgModuleIdentityResolutionPrecompAction_secondPrimitive :
    (Cochain.ofHom ((λ_ _).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq ▷ _)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y) (zero_add (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_leftUnit (RightModule R E) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E X M a hs hq) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom_replacement R E X M a hs hq) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y)

lemma dgModuleIdentityResolutionPrecompAction_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y _
      (dgModuleIdentityResolutionPrecompAction R E X Y M a hs hq) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E X M a hs hq) Y := by
  rw [dgModuleIdentityResolutionPrecompAction,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleIdentityResolutionPrecompAction_firstPrimitive,
    dgModuleIdentityResolutionPrecompAction_secondPrimitive, zero_add]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
