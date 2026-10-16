module

public import SerrePositivity.CategoryTheory.NerveVertices
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension

/-! # One comparison family on all factorization chains

The small fixed-boundary choice space supplies all finite fillers. They are
assembled once over the entire, possibly larger, factorization nerve. Each
finite simplex is then read back as a map into the original small space.
The existing factorization points are retained as prescribed vertices.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V)

abbrev choiceSpace : SSet.{v} := postChoiceSpace X Y V f g

abbrev point (a : ArrowFactorization g) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ choiceSpace f g :=
  CoherentLiftPostComposition.middlePoint hcof X Y a.middle V f a.left a.right ≫
    PostCompositionChain.choiceCast f a.fac

abbrev liftedPoint (a : ArrowFactorization g) :
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶ UniverseLift.obj.{u} (choiceSpace f g) :=
  (UniverseLift.stdIso.{u, v} 0).inv ≫ UniverseLift.map (point hcof f g a)

abbrev vertexData : NerveVertices.vertices.{v, max u v} (ArrowFactorization g) ⟶
    UniverseLift.obj.{u} (choiceSpace f g) :=
  VertexTuples.pointsMap (fun a : ULift.{v} (ArrowFactorization g) => liftedPoint hcof f g a.down)

def comparison : nerve (ArrowFactorization g) ⟶ UniverseLift.obj.{u} (choiceSpace f g) :=
  LargeParameterExtension.relativeExtend hcof hfib (vertexInclusion X Y f) (postBoundary X Y V f g)
    (ResolutionLiftSpace.projection X V (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ g.base))
    (NerveVertices.inclusion (ArrowFactorization g)) (vertexData hcof f g)

@[reassoc]
lemma comparison_vertices : NerveVertices.inclusion (ArrowFactorization g) ≫
    comparison hcof hfib f g = vertexData hcof f g :=
  LargeParameterExtension.relativeExtend_initial _ _ _ _ _ _ _ _

@[reassoc]
lemma comparison_point (a : ArrowFactorization g) :
    SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a) ≫ comparison hcof hfib f g =
      liftedPoint hcof f g a := by
  rw [← NerveVertices.vertex_inclusion, Category.assoc, comparison_vertices,
    VertexTuples.vertex_pointsMap]

abbrev chainComparison : AnchoredChain.simplicial g ⟶ UniverseLift.obj.{u} (choiceSpace f g) :=
  (AnchoredChain.nerveIso g).inv ≫ comparison hcof hfib f g

/-- Every simplex has a value in the original Hom universe. -/
def simplex {n : ℕ} (c : AnchoredChain g n) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ choiceSpace f g :=
  SSet.yonedaEquiv.symm
    (((chainComparison hcof hfib f g).app (Opposite.op (SimplexCategory.mk n)) c).down)

/-- A single global choice enforces every face and degeneracy identity. -/
lemma simplex_naturality {n m : ℕ} (c : AnchoredChain g n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof hfib f g c =
      simplex hcof hfib f g (c.reindex θ.toOrderHom) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_naturality]
  simp only [simplex, Equiv.apply_symm_apply]
  exact (congrArg ULift.down (congrArg (fun q => q c)
    ((chainComparison hcof hfib f g).naturality θ.op))).symm

lemma simplex_fixed_boundary {n : ℕ} (c : AnchoredChain g n) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
        (simplex hcof hfib f g c) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y V f g :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

lemma action_naturality {n m : ℕ} (c : AnchoredChain g n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (cosimplicialHom V.resolution.obj).obj Z) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map θ ≫
      KanLiftAction.parameterized hcof hfib X V (f ≫ g.base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
          (simplex hcof hfib f g c)) t =
      KanLiftAction.parameterized hcof hfib X V (f ≫ g.base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
          (simplex hcof hfib f g (c.reindex θ.toOrderHom)))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map θ) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    simplex_naturality]

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationComparison
