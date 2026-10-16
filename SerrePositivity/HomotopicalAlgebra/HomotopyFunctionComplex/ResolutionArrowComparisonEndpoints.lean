module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveArrowComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation

/-! # Actual all-center comparison endpoints retaining the old whole tuple interpolations -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram ResolutionArrowTuples ResolutionArrowTupleCoherence

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev parameter := NerveArrowComparison.source (bigTuples C)
abbrev values := NerveArrowComparison.target (fibers C)
abbrev vertexParameter := NerveArrowComparison.source (bigVertices C)
abbrev vertexInclusion : vertexParameter C ⟶ parameter C :=
  NerveArrowComparison.sourceMap (bigInclusion C)
abbrev vertexBoundary : vertexParameter C ⟶ NerveMovingParameter.lifted.{u} (values C) :=
  NerveArrowComparison.boundary (bigVertices C) (NerveMovingParameter.lifted (fibers C))
    (bigBoundary C)

/-- Both endpoints are transported restrictions of the same existing whole all-center system. -/
def left : NerveMovingParameter.System.{u, v} (parameter C) (values C) :=
  NerveArrowComparison.left (bigTuples C) (NerveMovingParameter.lifted (fibers C))
    (system C hcof)

def right : NerveMovingParameter.System.{u, v} (parameter C) (values C) :=
  NerveArrowComparison.right (bigTuples C) (NerveMovingParameter.lifted (fibers C))
    (system C hcof)

lemma left_vertices : left C hcof ≫ NerveBiparameterMaps.restriction
    (vertexParameter C) (parameter C) (NerveMovingParameter.lifted (values C))
      (vertexInclusion C) = NerveNaturalBoundary.ofNatTrans
        (vertexParameter C) (NerveMovingParameter.lifted (values C)) (vertexBoundary C) :=
  NerveArrowComparison.left_boundary _ _ _ (bigInclusion C) (bigBoundary C)
    (system C hcof) (vertices_fixed C hcof)

lemma right_vertices : right C hcof ≫ NerveBiparameterMaps.restriction
    (vertexParameter C) (parameter C) (NerveMovingParameter.lifted (values C))
      (vertexInclusion C) = NerveNaturalBoundary.ofNatTrans
        (vertexParameter C) (NerveMovingParameter.lifted (values C)) (vertexBoundary C) :=
  NerveArrowComparison.right_boundary _ _ _ (bigInclusion C) (bigBoundary C)
    (system C hcof) (vertices_fixed C hcof)

lemma left_evaluate (e : Arrow (Index C)) :
    NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e =
      oldFamily C hcof e.left ≫ UniverseLift.map.{u} ((fibers C).map e.hom) := by
  change NerveMovingParameter.evaluate (parameter C) (values C)
    (NerveBiparameterMaps.mapTarget _ _ _
      (Functor.whiskerRight (NerveArrowComparison.transport (fibers C))
        SSet.uliftFunctor.{u, v})
      (NerveBiparameterMaps.reindex _ _ Arrow.leftFunc (system C hcof))) e = _
  rw [NerveBiparameterMaps.evaluate_mapTarget, NerveBiparameterMaps.evaluate_reindex,
    system_evaluate]
  rfl

lemma right_evaluate (e : Arrow (Index C)) :
    NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e =
      (bigTuples C).map e.hom ≫ oldFamily C hcof e.right := by
  change NerveMovingParameter.evaluate (parameter C) (values C)
    (NerveBiparameterMaps.restrict _ _ _ (NerveArrowComparison.transport (bigTuples C))
      (NerveBiparameterMaps.reindex _ _ Arrow.rightFunc (system C hcof))) e = _
  rw [NerveBiparameterMaps.evaluate_restrict, NerveBiparameterMaps.evaluate_reindex,
    system_evaluate]
  rfl

/-- Recover the actual original small interpolation followed by actual fiber transport. -/
lemma left_recover (e : Arrow (Index C)) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e) =
    CoherentLiftTuples.interpolation hcof (source C e.left).inner (target C e.left)
      (arrow C e.left) ≫ (fibers C).map e.hom := by
  rw [left_evaluate, ← UniverseLift.map_comp]
  exact UniverseLift.lower_map _

/-- Recover actual tuple transport followed by the actual original small interpolation. -/
lemma right_recover (e : Arrow (Index C)) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e) =
    (tuples C).map e.hom ≫ CoherentLiftTuples.interpolation hcof
      (source C e.right).inner (target C e.right) (arrow C e.right) := by
  rw [right_evaluate]
  change UniverseLift.lower (UniverseLift.map.{u} ((tuples C).map e.hom) ≫
    UniverseLift.map.{u} (CoherentLiftTuples.interpolation hcof _ _ _)) = _
  rw [← UniverseLift.map_comp]
  exact UniverseLift.lower_map _

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints
