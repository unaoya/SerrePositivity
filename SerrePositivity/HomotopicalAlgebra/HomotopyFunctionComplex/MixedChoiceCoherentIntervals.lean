module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveIntervalBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility

/-! # Coherent mixed intervals retaining all four old comparisons and shared endpoints

Each original interval is recovered whole at every mixed context. The
four edge systems and the common diagonal use the same four independently
constructed coherent endpoint systems, including along identity context maps.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals
inductive Vertex where
  | A | B | C | D

inductive Edge where
  | AB | BD | AC | CD | AD

def source : Edge → Vertex
  | .AB | .AC | .AD => .A
  | .BD => .B
  | .CD => .C

def target : Edge → Vertex
  | .AB => .B
  | .AC => .C
  | .BD | .CD | .AD => .D

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

abbrev values := MixedChoiceFunctor.existingFunctor Y W g hcof

def point (j : Vertex) (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (values hcof Y W g).obj t :=
  match j with
  | .A => CoherentLiftMixedComparison.pointA hcof t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .B => CoherentLiftMixedComparison.pointB hcof t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .C => CoherentLiftMixedComparison.pointC hcof t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .D => CoherentLiftMixedComparison.pointD hcof t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)

def oldEdge (e : Edge) (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (values hcof Y W g).obj t :=
  match e with
  | .AB => CoherentLiftMixedComparison.edgeAB hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .BD => CoherentLiftMixedComparison.edgeBD hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .AC => CoherentLiftMixedComparison.edgeAC hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .CD => CoherentLiftMixedComparison.edgeCD hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  | .AD => CoherentLiftMixedComparison.diagonal hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)

lemma oldEdge_zero (e : Edge) (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ oldEdge hcof hfib Y W g e t =
      point hcof Y W g (source e) t := by
  cases e
  · exact CoherentLiftMixedComparison.edgeAB_zero hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeBD_zero hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeAC_zero hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeCD_zero hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.diagonal_zero hcof hfib
      t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)

lemma oldEdge_one (e : Edge) (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ oldEdge hcof hfib Y W g e t =
      point hcof Y W g (target e) t := by
  cases e
  · exact CoherentLiftMixedComparison.edgeAB_one hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeBD_one hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeAC_one hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.edgeCD_one hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  · exact CoherentLiftMixedComparison.diagonal_one hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)

include hfib in
lemma projection_trivialFibration (t : MixedChoiceFunctor.Context Y W) :
    trivialFibrations SSet.{v} ((NerveCoherentExtension.projection (values hcof Y W g)).app t) := by
  have he : (NerveCoherentExtension.projection (values hcof Y W g)).app t =
      (MixedChoiceFunctor.choiceIso Y W g hcof t).inv ≫
        (MixedChoiceFunctor.projection Y W g hcof).app t :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact (trivialFibrations SSet.{v}).comp_mem _ _
    ((trivialFibrations SSet.{v}).of_isIso (MixedChoiceFunctor.choiceIso Y W g hcof t).inv)
    (MixedChoiceFunctor.projection_trivialFibration Y W g hcof hfib t)

/-- Choose the four endpoint systems once, before choosing any interval extension. -/
abbrev endpoint (j : Vertex) :=
  NerveIntervalBoundary.chosenEndpoint (values hcof Y W g) hcof
    (projection_trivialFibration hcof hfib Y W g) (point hcof Y W g j)

lemma endpoint_point (j : Vertex) (t : MixedChoiceFunctor.Context Y W) :
    (endpoint hcof hfib Y W g j).app
      (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ t)) = point hcof Y W g j t :=
  NerveLowerExtension.extendVertices_point _ _ _ _ t

/-- All four old comparisons extend, using exactly these shared whole endpoint systems. -/
def interval (e : Edge) : NerveParameterExtension.System (values hcof Y W g)
    (SSet.stdSimplex.obj (SimplexCategory.mk 1)) :=
  NerveIntervalBoundary.betweenChosen (values hcof Y W g)
    (point hcof Y W g (source e)) (point hcof Y W g (target e)) (oldEdge hcof hfib Y W g e)
    (oldEdge_zero hcof hfib Y W g e) (oldEdge_one hcof hfib Y W g e) hcof hfib
    (projection_trivialFibration hcof hfib Y W g)

lemma interval_evaluate (e : Edge) (t : MixedChoiceFunctor.Context Y W) :
    NerveParameterExtension.evaluate (values hcof Y W g) (interval hcof hfib Y W g e) t =
      oldEdge hcof hfib Y W g e t :=
  NerveIntervalBoundary.betweenChosen_evaluate _ _ _ _ _ _ _ _ _ t

lemma interval_component (e : Edge)
    (s : Reedy.Lower (NerveCoherentFamily.reedy (MixedChoiceFunctor.Context Y W)) 1) :
    (interval hcof hfib Y W g e).app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.name (oldEdge hcof hfib Y W g e (NerveSimplexEndpoint.endpoint s.obj)) :=
  congr_app (NerveIntervalBoundary.betweenChosen_restrict (values hcof Y W g)
    (point hcof Y W g (source e)) (point hcof Y W g (target e)) (oldEdge hcof hfib Y W g e)
    (oldEdge_zero hcof hfib Y W g e) (oldEdge_one hcof hfib Y W g e) hcof hfib
    (projection_trivialFibration hcof hfib Y W g)) s

lemma interval_zero (e : Edge) : interval hcof hfib Y W g e ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 2))) =
    NerveIntervalBoundary.constant (values hcof Y W g) BoundaryOneCotensor.vertex
      (endpoint hcof hfib Y W g (source e)) :=
  NerveIntervalBoundary.betweenChosen_zero _ _ _ _ _ _ _ _ _

lemma interval_one (e : Edge) : interval hcof hfib Y W g e ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (0 : Fin 2))) =
    NerveIntervalBoundary.constant (values hcof Y W g) BoundaryOneCotensor.vertex
      (endpoint hcof hfib Y W g (target e)) :=
  NerveIntervalBoundary.betweenChosen_one _ _ _ _ _ _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals
