module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedPullback
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-! 二項直和は零複体の上の引き戻しであり、同じ実空間模型もこの正方形を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable {R : Type u} [CommRing R] (P Q : Complex R)

lemma dgGluingComplexBiprod_isPullback :
    IsPullback (biprod.fst : P ⊞ Q ⟶ P) (biprod.snd : P ⊞ Q ⟶ Q)
      (0 : P ⟶ (0 : Complex R)) (0 : Q ⟶ (0 : Complex R)) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T f g h₀ h₁
    exact biprod.hom_ext f g h₀ h₁
  · intro T f g h
    exact ⟨biprod.lift f g, biprod.lift_fst _ _, biprod.lift_snd _ _⟩

lemma dgGluingComplexPinchedBiprod_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.fst : P ⊞ Q ⟶ P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.snd : P ⊞ Q ⟶ Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (0 : P ⟶ (0 : Complex R)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (0 : Q ⟶ (0 : Complex R))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedMap_isPullback (dgGluingComplexBiprod_isPullback P Q)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
