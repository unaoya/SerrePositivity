module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-! # One all-center coherent family retaining the original tuple interpolations

The old tuple maps and their actual strict-vertex boundary are retained,
including every higher tuple simplex. A natural vertex boundary supplies
the whole fixed boundary system without another coherence assumption.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram
open SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev bigTuples := tuples C ⋙ SSet.uliftFunctor.{u, v}
abbrev bigVertices := vertices C ⋙ SSet.uliftFunctor.{u, v}
abbrev bigInclusion : bigVertices C ⟶ bigTuples C :=
  Functor.whiskerRight (inclusion C) SSet.uliftFunctor.{u, v}
abbrev bigBoundary : bigVertices C ⟶ NerveMovingParameter.lifted.{u} (fibers C) :=
  Functor.whiskerRight (vertexData C) SSet.uliftFunctor.{u, v}

abbrev oldFamily (q : Index C) : (bigTuples C).obj q ⟶
    UniverseLift.obj.{u} ((fibers C).obj q) :=
  UniverseLift.map.{u} (CoherentLiftTuples.interpolation hcof (source C q).inner
    (target C q) (arrow C q))

lemma oldFamily_boundary (q : Index C) : (bigInclusion C).app q ≫ oldFamily C hcof q =
    (bigBoundary C).app q := by
  change UniverseLift.map.{u} (VertexTuples.inclusion (StrictLift C q)) ≫
    UniverseLift.map.{u} (CoherentLiftTuples.interpolation hcof (source C q).inner
      (target C q) (arrow C q)) = UniverseLift.map.{u} _
  rw [← UniverseLift.map_comp]
  exact congrArg (fun e => UniverseLift.map.{u} e)
    (CoherentLiftTuples.interpolation_vertices hcof (source C q).inner (target C q) (arrow C q))

omit [ModelCategory SSet.{v}] in
lemma bigInclusion_mono (q : Index C) : Mono ((bigInclusion C).app q) :=
  UniverseLift.mono_map _

/-- All old interpolation maps are fixed at once, with all strict vertices fixed in all degrees. -/
def system : NerveMovingParameter.System.{u, v} (bigTuples C) (fibers C) :=
  NerveRelativeNaturalBoundary.extend (bigVertices C) (bigTuples C) (fibers C)
    (bigInclusion C) (bigBoundary C) (oldFamily C hcof) (oldFamily_boundary C hcof)
    (fillers C hcof) (bigInclusion_mono C)

lemma system_evaluate (q : Index C) : NerveMovingParameter.evaluate.{u, v}
    (bigTuples C) (fibers C) (system C hcof) q = oldFamily C hcof q :=
  NerveRelativeNaturalBoundary.extend_evaluate _ _ _ _ _ _ _ _ _ q

/-- Recover the actual original small tuple interpolation, as a full map. -/
lemma interpolation_recover (q : Index C) : UniverseLift.lower
    (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    CoherentLiftTuples.interpolation hcof (source C q).inner (target C q) (arrow C q) := by
  rw [system_evaluate]
  exact UniverseLift.lower_map _

lemma vertices_fixed : system C hcof ≫ NerveMovingParameterRelative.restriction
    (bigVertices C) (bigTuples C) (bigInclusion C) (fibers C) =
    NerveNaturalBoundary.ofNatTrans (bigVertices C)
      (NerveMovingParameter.lifted (fibers C)) (bigBoundary C) :=
  NerveRelativeNaturalBoundary.extend_boundary _ _ _ _ _ _ _ _ _

lemma vertex_component (s : NerveSimplexEndpoint.Index (Index C)) : (system C hcof).app s ≫
    (CategoryTheory.MonoidalClosed.pre
      ((bigInclusion C).app (NerveSimplexStart.start s))).app
        (UniverseLift.obj.{u} ((fibers C).obj (NerveSimplexEndpoint.endpoint s))) =
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
      ((bigBoundary C).app (NerveSimplexStart.start s) ≫
        (NerveMovingParameter.lifted (fibers C)).map (NerveNaturalBoundary.whole s)) := by
  have h := congr_app (vertices_fixed C hcof) s
  exact h

lemma simplex_recover (q : Index C) {n : ℕ} (a : Fin (n + 1) → StrictLift C q) :
    VertexTuples.simplex a ≫ UniverseLift.lower
      (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    CoherentLiftTuples.simplex hcof (source C q).inner (target C q) (arrow C q) a := by
  rw [interpolation_recover]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
