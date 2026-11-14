module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.TwoEndpointPathLift

/-! 元の差の cocone は、二合成を始終点とする path 複体の厳密な引き戻し。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q K : Complex R} (a b : P ⟶ Q)

lemma dgGluingTwoEndpointPath_hom_ext (f g : K ⟶ mappingCocone (b - a))
    (hp : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b = g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b)
    (hb : f ≫ mappingCocone.fst (b - a) = g ≫ mappingCocone.fst (b - a)) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePath_hom_ext (b - a) f g _ hb
  have h := congrArg (fun k => k ≫ biprod.snd) hp
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath, Category.assoc, biprod.lift_snd] using h

def dgGluingTwoEndpointPathPullbackCone :
    PullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q) (biprod.lift a b) :=
  PullbackCone.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b) (mappingCocone.fst (b - a))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath_endpoints a b)

def dgGluingTwoEndpointPathPullbackCone_isLimit :
    IsLimit (dgGluingTwoEndpointPathPullbackCone a b) :=
  PullbackCone.IsLimit.mk _
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathLift a b s.fst s.snd s.condition)
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathLift_path a b s.fst s.snd s.condition)
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathLift_base a b s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => dgGluingTwoEndpointPath_hom_ext a b m _
      (hm₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathLift_path a b s.fst s.snd s.condition).symm)
      (hm₂.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathLift_base a b s.fst s.snd s.condition).symm))

lemma dgGluingTwoEndpointPath_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b) (mappingCocone.fst (b - a))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q) (biprod.lift a b) :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath_endpoints a b⟩,
    ⟨dgGluingTwoEndpointPathPullbackCone_isLimit a b⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
