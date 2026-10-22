module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedBiprodNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathSpace

/-! 元の二端点写像を、同じ係数空間の直積へ値を保って移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingComplexPathSpaceEndpointPair :
    complexPinchedSpace.{u, v} (dgGluingComplexPath Q) ⟶
      complexPinchedSpace.{u, v} Q ⊗ complexPinchedSpace.{u, v} Q :=
  lift (complexPinchedMap.{u, v} (dgGluingComplexPathStart Q))
    (complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q))

lemma dgGluingComplexPathSpaceEndpointPair_eq :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q =
      complexPinchedMap.{u, v} (dgGluingComplexPathEndpoints Q) ≫
        (dgGluingComplexPinchedBiprodIso.{u, v} Q Q).hom :=
  (dgGluingComplexPinchedBiprodIso_lift _ _).symm

lemma dgGluingComplexPathSpaceEndpointPair_fibration :
    Fibration (dgGluingComplexPathSpaceEndpointPair.{u, v} Q) := by
  rw [dgGluingComplexPathSpaceEndpointPair_eq]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B i hi
  let : HasLiftingProperty i (complexPinchedMap.{u, v} (dgGluingComplexPathEndpoints Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1
      (dgGluingComplexPathSpaceEndpoints_fibration Q) i hi
  infer_instance

lemma dgGluingComplexPathSpaceEndpointPair_start :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q ≫ fst _ _ =
      complexPinchedMap.{u, v} (dgGluingComplexPathStart Q) :=
  lift_fst _ _

lemma dgGluingComplexPathSpaceEndpointPair_end :
    dgGluingComplexPathSpaceEndpointPair.{u, v} Q ≫ snd _ _ =
      complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q) :=
  lift_snd _ _

end SerrePositivity.InfinityCategories
