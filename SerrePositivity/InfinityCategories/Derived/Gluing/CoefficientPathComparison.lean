module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPathSpaceHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyEquivalencePath

/-! 係数複体の同じ二端点 path を、係数空間内の元の区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingCoefficientPathComparison :
    complexPinchedSpace.{u, v} (dgGluingComplexPath Q) ⟶
      equivalencePath (complexPinchedSpace.{u, v} Q) :=
  F1B.kanHomotopyEquivalencePath (dgGluingComplexPathSpaceHomotopy Q)
    (dgGluingComplexPathSpaceHomotopy_invertible Q)

lemma dgGluingCoefficientPathComparison_start :
    dgGluingCoefficientPathComparison.{u, v} Q ≫
        equivalencePathEndpoint (complexPinchedSpace.{u, v} Q) 0 =
      complexPinchedMap.{u, v} (dgGluingComplexPathStart Q) :=
  F1B.kanHomotopyEquivalencePath_zero _ _

lemma dgGluingCoefficientPathComparison_end :
    dgGluingCoefficientPathComparison.{u, v} Q ≫
        equivalencePathEndpoint (complexPinchedSpace.{u, v} Q) 1 =
      complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q) :=
  F1B.kanHomotopyEquivalencePath_one _ _

lemma dgGluingCoefficientPathComparison_family :
    dgGluingCoefficientPathComparison.{u, v} Q ≫
        equivalencePathι (complexPinchedSpace.{u, v} Q) =
      curry ((β_ (Δ[1] : SSet.{max u v})
        (complexPinchedSpace.{u, v} (dgGluingComplexPath Q))).hom ≫
          (dgGluingComplexPathSpaceHomotopy.{u, v} Q).h) :=
  F1B.kanHomotopyEquivalencePath_ι _ _

end SerrePositivity.InfinityCategories
