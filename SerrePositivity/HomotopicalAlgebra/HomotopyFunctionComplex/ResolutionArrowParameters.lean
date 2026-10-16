module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative

/-! # All-center coherent families with the actual moving factorization parameter

Parameters change with each central arrow. A chain's parameter comes from
its first center and its small value from the last center. No constant
parameter or model structure on large auxiliary values is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev parameters : ResolutionArrowDiagram.Index C ⥤ SSet.{max u v} :=
  ResolutionArrowDiagram.baseIndex C ⋙ ArrowContext.parameters C

lemma parameter_map {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) :
    (parameters C).map f = AnchoredChain.mapFunctor
      (ArrowContext.factorizationMap ((ResolutionArrowDiagram.baseIndex C).map f)) := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (families : ∀ q, (parameters C).obj q ⟶
    UniverseLift.obj.{u} ((ResolutionArrowDiagram.fibers C).obj q))

/-- Retain every whole original family on its moving central-arrow parameter. -/
def system : NerveMovingParameter.System.{u, v} (parameters C)
    (ResolutionArrowDiagram.fibers C) :=
  NerveMovingParameter.extendFamilies.{u, v} (parameters C) (ResolutionArrowDiagram.fibers C)
    (ResolutionArrowDiagram.fillers C hcof) families

lemma system_evaluate (q : ResolutionArrowDiagram.Index C) :
    NerveMovingParameter.evaluate.{u, v} (parameters C) (ResolutionArrowDiagram.fibers C)
      (system C hcof families) q = families q :=
  NerveMovingParameter.extendFamilies_evaluate _ _ _ _ q

lemma system_compatibility {s t : Index (ResolutionArrowDiagram.Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ (system C hcof families).app t =
      (system C hcof families).app s ≫
        (CategoryTheory.MonoidalClosed.pre ((parameters C).map (NerveSimplexStart.startMap f))).app
          (UniverseLift.obj.{u} ((ResolutionArrowDiagram.fibers C).obj (endpoint s))) ≫
        (CategoryTheory.ihom ((parameters C).obj (NerveSimplexStart.start t))).map
          (UniverseLift.map.{u} ((ResolutionArrowDiagram.fibers C).map (endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters
