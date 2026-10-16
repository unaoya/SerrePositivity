module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveEvaluationLaws
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit

/-! # Whole cylinder fit derived from the actual two endpoints and entire vertex restriction -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary NerveCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma zero_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (zeroInclusion C).app e ≫ NerveMovingParameter.evaluate (boundaryParameter C) (values C)
      (system C hcof) e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_zero C hcof) e).trans
    (NerveEvaluationLaws.expand _ _ _ _ e)

lemma one_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (oneInclusion C).app e ≫ NerveMovingParameter.evaluate (boundaryParameter C) (values C)
      (system C hcof) e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_one C hcof) e).trans
    (NerveEvaluationLaws.expand _ _ _ _ e)

lemma vertex_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (NerveCylinderBoundary.vertexInclusion (vertexParameter C) (parameter C)
      (vertexInclusion C) boundaryMap.{max u v}).app e ≫
        NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_vertices C hcof) e).trans
    (NerveEvaluationLaws.natural _ _ _ e)

variable (e : Arrow (ResolutionArrowDiagram.Index C))
  (H : (fullParameter C).obj e ⟶ UniverseLift.obj.{u} ((values C).obj e))
  (hzero : (zeroInclusion C ≫ inclusion C).app e ≫ H =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e)
  (hone : (oneInclusion C ≫ inclusion C).app e ≫ H =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e)
  (hvertex : (horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app e ≫ H =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e)

include hzero hone hvertex in
lemma pointwise_fit : (inclusion C).app e ≫ H =
    NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e := by
  apply (NervePushoutBoundary.square
    (product (vertexParameter C) ends.{max u v}) (product (parameter C) ends.{max u v})
    (product (vertexParameter C) interval.{max u v})
    (horizontal (vertexParameter C) (parameter C) (vertexInclusion C) ends.{max u v})
    (vertical boundaryMap.{max u v} (vertexParameter C)) e).hom_ext
  · apply (NerveMovingIntervalBoundary.coproduct (parameter C) e).hom_ext
    intro j
    rcases j with ⟨j⟩
    cases j
    · change (vertical NerveMovingIntervalBoundary.zero (parameter C)).app e ≫
        (endpointInclusion (vertexParameter C) (parameter C)
          (vertexInclusion C) boundaryMap.{max u v}).app e ≫
            (inclusion C).app e ≫ H =
        (vertical NerveMovingIntervalBoundary.zero (parameter C)).app e ≫
          (endpointInclusion (vertexParameter C) (parameter C)
            (vertexInclusion C) boundaryMap.{max u v}).app e ≫
              NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e
      simpa only [NatTrans.comp_app, zeroInclusion, Category.assoc] using
        hzero.trans (zero_evaluate C hcof e).symm
    · change (vertical NerveMovingIntervalBoundary.one (parameter C)).app e ≫
        (endpointInclusion (vertexParameter C) (parameter C)
          (vertexInclusion C) boundaryMap.{max u v}).app e ≫
            (inclusion C).app e ≫ H =
        (vertical NerveMovingIntervalBoundary.one (parameter C)).app e ≫
          (endpointInclusion (vertexParameter C) (parameter C)
            (vertexInclusion C) boundaryMap.{max u v}).app e ≫
              NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e
      simpa only [NatTrans.comp_app, oneInclusion, Category.assoc] using
        hone.trans (one_evaluate C hcof e).symm
  · have hfac := congr_app (NerveCylinderBoundary.vertexInclusion_inclusion
      (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) e
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ H) hfac)).trans
      (hvertex.trans (vertex_evaluate C hcof e).symm)


/-- Independent entire interval maps with their actual two endpoint and whole vertex equations. -/
structure Data where
  family : ∀ e, (fullParameter C).obj e ⟶ UniverseLift.obj.{u} ((values C).obj e)
  zero : ∀ e, (zeroInclusion C ≫ inclusion C).app e ≫ family e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e
  one : ∀ e, (oneInclusion C ≫ inclusion C).app e ≫ family e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e
  vertex : ∀ e, (horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app e ≫ family e =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e

variable (d : Data C hcof)

lemma family_fit (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (inclusion C).app e ≫ d.family e =
      NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e :=
  pointwise_fit C hcof e (d.family e) (d.zero e) (d.one e) (d.vertex e)

/-- Preserve every original whole interval map and the entire fixed coherent boundary together. -/
def extendFamilies : NerveMovingParameter.System.{u, v} (fullParameter C) (values C) :=
  NerveMovingFamilyFit.extend (fullParameter C) (values C) (boundaryParameter C)
    (inclusion C) d.family (system C hcof) (family_fit C hcof d)
    (fun e => ResolutionArrowDiagram.fillers C hcof e.right)
    (ResolutionArrowCylinderBoundary.inclusion_mono C)

lemma extendFamilies_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    NerveMovingParameter.evaluate (fullParameter C) (values C) (extendFamilies C hcof d) e =
      d.family e := NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ e

lemma extendFamilies_boundary : extendFamilies C hcof d ≫
    NerveMovingParameterRelative.restriction (boundaryParameter C) (fullParameter C)
      (inclusion C) (values C) = system C hcof :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit
