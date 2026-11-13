module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeTwoEndpointPath

/-! 同じ二端点を持つ path と基底の射から、元の差の cocone への実持ち上げを構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q K : Complex R} (a b : P ⟶ Q)
  (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q) (g : K ⟶ P)
  (h : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q = g ≫ biprod.lift a b)

include h in
lemma dgGluingTwoEndpointPath_start_condition : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q = g ≫ a := by
  have hc := congrArg (fun k => k ≫ biprod.fst) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, Category.assoc, biprod.lift_fst] using hc

include h in
lemma dgGluingTwoEndpointPath_end_condition : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q = g ≫ b := by
  have hc := congrArg (fun k => k ≫ biprod.snd) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, Category.assoc, biprod.lift_snd] using hc

include h in
lemma dgGluingTwoEndpointPath_difference_condition :
    (f ≫ biprod.snd) ≫ mappingCocone.fst (𝟙 Q) = g ≫ (b - a) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath_difference, Preadditive.comp_sub,
    dgGluingTwoEndpointPath_end_condition a b f g h,
    dgGluingTwoEndpointPath_start_condition a b f g h, Preadditive.comp_sub]

def dgGluingTwoEndpointPathLift : K ⟶ mappingCocone (b - a) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathLift (b - a) (f ≫ biprod.snd) g
    (dgGluingTwoEndpointPath_difference_condition a b f g h)

lemma dgGluingTwoEndpointPathLift_base :
    dgGluingTwoEndpointPathLift a b f g h ≫ mappingCocone.fst (b - a) = g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathLift_fst _ _ _ _

lemma dgGluingTwoEndpointPathLift_path :
    dgGluingTwoEndpointPathLift a b f g h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b = f := by
  apply biprod.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath, biprod.lift_fst,
      ← Category.assoc, dgGluingTwoEndpointPathLift_base]
    exact (dgGluingTwoEndpointPath_start_condition a b f g h).symm
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath, biprod.lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathLift_path _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
