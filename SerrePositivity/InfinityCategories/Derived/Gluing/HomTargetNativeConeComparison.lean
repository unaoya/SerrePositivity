module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityCone
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityNativeConeComparison
/-! 元共通終域への lax 比較と、同じ元の実 cone 関手の全自然比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants F2.Idempotent
variable (R : Type u) [CommRing R]
  (C D E : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E] [IsDGPretriangulated R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local instance dgGluingHomTargetNativeConeBase_stable : IsStable (dgNerve R E) :=
  dgNerve_isStable_of_pretriangulated R E

def dgGluingHomTargetNativeConeComparison (hE : IsIdempotentComplete (dgNerve R E))
    (z : E) (hz : IsZero (ForgetEnrichment.of (Complex R) z)) : FunctorIso
    ((dgGluingHomTargetNerveLaxComparison.{u, 0} R C D E p q ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E)
        (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))) ≫
      dgNerve.map (dgPerfectYoneda R E))
    (dgNerve.map (dgHomGluingConeFunctor R C D E p q)) := by
  let f := dgNerve.map (dgGluingHomTargetToIdentity R C D E p q)
  let e := dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R E
  let a := dgGluingHomTargetAugmentationArrowFamily.{u, 0} R C D E p q
  let y := dgNerve.map (dgPerfectYoneda R E)
  let arrow := F2.laxPullbackArrow (𝟙 (dgNerve R E)) (𝟙 (dgNerve R E))
  let δ := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) arrow
  have ha : (f ≫ e.hom) ≫ arrow = a := by
    rw [Category.assoc, dgGluingIdentityHomTargetLaxEquivalence_arrow]
    exact dgGluingHomTargetToIdentity_arrow.{u, 0} R C D E p q
  have h₁ : FunctorIso (((f ≫ e.hom) ≫ δ) ≫ y)
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) a ≫ y) := by
    have h := (CofiberFamily.precompositionIso arrow (f ≫ e.hom)).postcomp y
    exact F2.functorIsoOfEq h rfl (congrArg (fun t =>
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) t ≫ y) ha)
  have h₂ : FunctorIso (((f ≫ e.hom) ≫ δ) ≫ y)
      (f ≫ dgNerve.map (dgHomGluingConeFunctor R E E E
        (DGFunctor.id E) (DGFunctor.id E))) := by
    have h := (dgGluingIdentityNativeConeComparison R E hE z hz).precomp f
    exact F2.functorIsoOfEq h
      ((Category.assoc f (e.hom ≫ δ) y).symm.trans
        (congrArg (fun k => k ≫ y) (Category.assoc f e.hom δ).symm)) rfl
  have hf : f ≫ dgNerve.map (dgHomGluingConeFunctor R E E E
        (DGFunctor.id E) (DGFunctor.id E)) =
      dgNerve.map (dgHomGluingConeFunctor R C D E p q) := by
    rw [← dgNerve.map_comp, dgGluingHomTargetToIdentity_cone]
  have h₃ : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) a ≫ y)
      (dgNerve.map (dgHomGluingConeFunctor R C D E p q)) :=
    F2.functorIsoOfEq (h₁.symm.trans h₂) rfl hf
  have h₀ := (CofiberFamily.precompositionIso
    (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))
    (dgGluingHomTargetNerveLaxComparison.{u, 0} R C D E p q)).postcomp y
  have h₀' : FunctorIso
      ((dgGluingHomTargetNerveLaxComparison.{u, 0} R C D E p q ≫
        _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E)
          (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))) ≫ y)
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) a ≫ y) :=
    F2.functorIsoOfEq h₀ rfl (congrArg (fun t =>
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (dgNerve R E) t ≫ y)
        (dgGluingHomTargetNerveLaxComparison_arrow.{u, 0} R C D E p q))
  exact h₀'.trans h₃

end SerrePositivity.InfinityCategories
