module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathLift

/-! 元の差の cocone は、二合成を始終点とする path 複体の厳密な引き戻し。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q K : Complex R} (a b : P ⟶ Q)

lemma dgGluingTwoEndpointPath_hom_ext (f g : K ⟶ mappingCocone (b - a))
    (hp : f ≫ dgGluingCoconeTwoEndpointPath a b = g ≫ dgGluingCoconeTwoEndpointPath a b)
    (hb : f ≫ mappingCocone.fst (b - a) = g ≫ mappingCocone.fst (b - a)) : f = g := by
  apply dgGluingCoconePath_hom_ext (b - a) f g _ hb
  have h := congrArg (fun k => k ≫ biprod.snd) hp
  simpa only [dgGluingCoconeTwoEndpointPath, Category.assoc, biprod.lift_snd] using h

def dgGluingTwoEndpointPathPullbackCone :
    PullbackCone (dgGluingComplexPathEndpoints Q) (biprod.lift a b) :=
  PullbackCone.mk (dgGluingCoconeTwoEndpointPath a b) (mappingCocone.fst (b - a))
    (dgGluingCoconeTwoEndpointPath_endpoints a b)

def dgGluingTwoEndpointPathPullbackCone_isLimit :
    IsLimit (dgGluingTwoEndpointPathPullbackCone a b) :=
  PullbackCone.IsLimit.mk _
    (fun s => dgGluingTwoEndpointPathLift a b s.fst s.snd s.condition)
    (fun s => dgGluingTwoEndpointPathLift_path a b s.fst s.snd s.condition)
    (fun s => dgGluingTwoEndpointPathLift_base a b s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => dgGluingTwoEndpointPath_hom_ext a b m _
      (hm₁.trans (dgGluingTwoEndpointPathLift_path a b s.fst s.snd s.condition).symm)
      (hm₂.trans (dgGluingTwoEndpointPathLift_base a b s.fst s.snd s.condition).symm))

lemma dgGluingTwoEndpointPath_isPullback :
    IsPullback (dgGluingCoconeTwoEndpointPath a b) (mappingCocone.fst (b - a))
      (dgGluingComplexPathEndpoints Q) (biprod.lift a b) :=
  ⟨⟨dgGluingCoconeTwoEndpointPath_endpoints a b⟩,
    ⟨dgGluingTwoEndpointPathPullbackCone_isLimit a b⟩⟩

end SerrePositivity.InfinityCategories
