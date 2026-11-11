module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedBiprodNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TwoEndpointPathSpace

/-! 元の二端点写像を、同じ係数空間の直積へ値を保って移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingComplexPathSpaceEndpointPair :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q :=
  lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q))

lemma dgGluingComplexPathSpaceEndpointPair_eq :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} Q Q).hom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso_lift _ _).symm

lemma dgGluingComplexPathSpaceEndpointPair_fibration :
    Fibration (dgGluingComplexPathSpaceEndpointPair.{u, v} Q) := by
  rw [dgGluingComplexPathSpaceEndpointPair_eq]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B i hi
  let : HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpoints_fibration Q) i hi
  infer_instance

lemma dgGluingComplexPathSpaceEndpointPair_start :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q ≫ fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q) :=
  lift_fst _ _

lemma dgGluingComplexPathSpaceEndpointPair_end :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q ≫ snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q) :=
  lift_snd _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
