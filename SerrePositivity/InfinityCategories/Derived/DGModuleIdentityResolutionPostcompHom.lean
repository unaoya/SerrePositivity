module
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPostcompData
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionIdentity
/-!
概要：入力が元の閉射、replacement が恒等、比較 cochain が零である実分解射を構成する。
方針：実二射影と mapping cocone の持ち上げを使う。
規約：分解変更比較の同定は別工程。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
variable (X : DGModuleFunctorResolutionObject R (RightModule R E) E
  (DGFunctor.id (A := R) (RightModule R E)))
  (M : RightModule R E)
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)
lemma dgModuleIdentityResolutionPostcomp_boundary :
    δ (-1) 0 (0 : Cochain (𝟙_ (Complex R))
      (moduleHom R E X.replacement.val
        ((DGFunctor.id (A := R) (RightModule R E)).obj
          (dgModuleIdentityResolutionPostcompObject R E X M a hs hq).source)) (-1)) +
      Cochain.ofHom (biprod.lift (ForgetEnrichment.homTo (Complex R) a)
        (eId (Complex R) X.replacement.val) ≫
        dgModuleFunctorResolutionDifference R (RightModule R E) E
          (DGFunctor.id (A := R) (RightModule R E)) X
          (dgModuleIdentityResolutionPostcompObject R E X M a hs hq)) = 0 := by
  rw [dgModuleIdentityResolutionPostcomp_difference]
  simp

def dgModuleIdentityResolutionPostcompHom :
    𝟙_ (Complex R) ⟶ dgModuleFunctorResolutionHomComplex R (RightModule R E) E
      (DGFunctor.id (A := R) (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) :=
  dgModuleFunctorResolutionHomLift R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)) X
    (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) _
    (ForgetEnrichment.homTo (Complex R) a) (eId (Complex R) X.replacement.val) 0
    (dgModuleIdentityResolutionPostcomp_boundary R E X M a hs hq)

lemma dgModuleIdentityResolutionPostcompHom_source :
    dgModuleIdentityResolutionPostcompHom R E X M a hs hq ≫
      dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (A := R) (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) =
      ForgetEnrichment.homTo (Complex R) a :=
  dgModuleFunctorResolutionHomLift_source R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)) X
    (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) _ _ _ _ _

lemma dgModuleIdentityResolutionPostcompHom_replacement :
    dgModuleIdentityResolutionPostcompHom R E X M a hs hq ≫
      dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (A := R) (RightModule R E)) X
        (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) =
      eId (Complex R) X.replacement.val :=
  dgModuleFunctorResolutionHomLift_replacement R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)) X
    (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) _ _ _ _ _

lemma dgModuleIdentityResolutionPostcompHom_comparison :
    dgModuleFunctorResolutionHomComparison R (RightModule R E) E
      (DGFunctor.id (A := R) (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) _
      (dgModuleIdentityResolutionPostcompHom R E X M a hs hq) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgModuleFunctorResolutionHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (dgModuleFunctorResolutionDifference R (RightModule R E) E
      (DGFunctor.id (A := R) (RightModule R E)) X
      (dgModuleIdentityResolutionPostcompObject R E X M a hs hq))
    (biprod.lift (ForgetEnrichment.homTo (Complex R) a)
      (eId (Complex R) X.replacement.val)) 0
    (dgModuleIdentityResolutionPostcomp_boundary R E X M a hs hq) p q hpq

end SerrePositivity.InfinityCategories
