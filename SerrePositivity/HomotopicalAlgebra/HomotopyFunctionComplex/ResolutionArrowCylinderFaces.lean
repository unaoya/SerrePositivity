module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary

/-! # The actual standard faces of the glued all-center cylinder boundary -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary NerveCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces
variable (C : Type u) [Category.{v} C] [ModelCategory C]

lemma zero : zeroInclusion C ≫ inclusion C =
    vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameter C) := by
  change (vertical NerveMovingIntervalBoundary.zero (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) ≫
      NerveCylinderBoundary.inclusion (vertexParameter C) (parameter C)
        (vertexInclusion C) boundaryMap.{max u v} = _
  rw [Category.assoc, endpointInclusion_inclusion]
  apply NatTrans.ext
  funext e
  change (parameter C).obj e ◁ SSet.boundary.ι (1 : Fin 2) ≫
    (parameter C).obj e ◁ (SSet.boundary 1).ι = (parameter C).obj e ◁ SSet.stdSimplex.δ 1
  rw [← MonoidalCategory.whiskerLeft_comp, SSet.boundary.ι_ι]

lemma one : oneInclusion C ≫ inclusion C =
    vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameter C) := by
  change (vertical NerveMovingIntervalBoundary.one (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) ≫
      NerveCylinderBoundary.inclusion (vertexParameter C) (parameter C)
        (vertexInclusion C) boundaryMap.{max u v} = _
  rw [Category.assoc, endpointInclusion_inclusion]
  apply NatTrans.ext
  funext e
  change (parameter C).obj e ◁ SSet.boundary.ι (0 : Fin 2) ≫
    (parameter C).obj e ◁ (SSet.boundary 1).ι = (parameter C).obj e ◁ SSet.stdSimplex.δ 0
  rw [← MonoidalCategory.whiskerLeft_comp, SSet.boundary.ι_ι]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces
