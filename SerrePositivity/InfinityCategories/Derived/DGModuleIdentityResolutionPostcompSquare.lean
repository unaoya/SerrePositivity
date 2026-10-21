module
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPostcompAction
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPrecompAction
/-!
概要：入力変更の実二経路の合成を、二射影と比較 cochain の一致から同定する。
方針：同じ実 Hom への射の一意性と、左右合成の全成分の計算を使う。
規約：全パラメータ複体からの等式。使われ方：分解変更の全 Hom 自然性。
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
  (M N : RightModule R E)
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) M)
  (b : ForgetEnrichment.of (Complex R) Y.source ⟶ ForgetEnrichment.of (Complex R) N)
  (ha : moduleDegreewiseSurjective R E a) (qa : moduleQuasiIso R E a)
  (hb : moduleDegreewiseSurjective R E b) (qb : moduleQuasiIso R E b)
  (K : Complex R)
  (f : K ⟶ dgModuleFunctorResolutionHomComplex R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) X Y)
  (g : K ⟶ dgModuleFunctorResolutionHomComplex R (RightModule R E) E
    (DGFunctor.id (RightModule R E))
    (dgModuleIdentityResolutionPostcompObject R E X M a ha qa)
    (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb))
lemma dgModuleIdentityResolutionPostcomp_square
    (hs : f ≫ dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.source) b =
      g ≫ dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E))
        (dgModuleIdentityResolutionPostcompObject R E X M a ha qa)
        (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb) ≫
          eHomWhiskerRight (Complex R) a (ForgetEnrichment.of (Complex R) N))
    (hr : f ≫ dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) X Y =
      g ≫ dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E))
        (dgModuleIdentityResolutionPostcompObject R E X M a ha qa)
        (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb))
    (ht : dgModuleFunctorResolutionHomComparison R (RightModule R E) E
        (DGFunctor.id (RightModule R E))
        (dgModuleIdentityResolutionPostcompObject R E X M a ha qa)
        (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb) K g =
      (dgModuleFunctorResolutionHomComparison R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) X Y K f).comp
        (Cochain.ofHom (eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) X.replacement.val) b)) (add_zero (-1))) :
    f ≫ dgModuleIdentityResolutionPostcompAction R E X Y N b hb qb =
      g ≫ dgModuleIdentityResolutionPrecompAction R E X
        (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb) M a ha qa := by
  apply dgModuleFunctorResolutionHom_ext R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) X
    (dgModuleIdentityResolutionPostcompObject R E Y N b hb qb)
  · rw [Category.assoc, dgModuleIdentityResolutionPostcompAction_source,
      Category.assoc, dgModuleIdentityResolutionPrecompAction_source]
    exact hs
  · rw [Category.assoc, dgModuleIdentityResolutionPostcompAction_replacement,
      Category.assoc, dgModuleIdentityResolutionPrecompAction_replacement]
    exact hr
  · rw [dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleIdentityResolutionPostcompAction_comparison,
      dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleIdentityResolutionPrecompAction_comparison]
    exact (ht.trans (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ (zero_add (-1)))).symm
end
end SerrePositivity.InfinityCategories
