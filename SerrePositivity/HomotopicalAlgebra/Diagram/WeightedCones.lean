module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveBifunctor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Weighted spaces of simplicial diagram cones

For a small diagram of simplicial sets W, tensoring a space with W
has an actual right adjoint. Projective cofibrancy of W makes this a
Quillen adjunction. No injective diagram model is assumed.
-/

@[expose] public section
noncomputable section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction SerrePositivity.Quillen
namespace SerrePositivity.DiagramModel.WeightedCones
variable (K : Type w) [SmallCategory K]
abbrev tensorDiagram (W : K ⥤ SSet.{w}) : SSet.{w} ⥤ (K ⥤ SSet.{w}) :=
  (pointwise K (curriedTensor SSet.{w})).flip.obj W

instance tensorDiagram_preservesColimits (W : K ⥤ SSet.{w}) :
    PreservesColimitsOfSize.{w,w} (tensorDiagram K W) := by
  apply preservesColimits_of_evaluation
  intro k
  change PreservesColimitsOfSize.{w,w} (tensorRight (W.obj k))
  infer_instance

instance tensorDiagram_isLeftAdjoint (W : K ⥤ SSet.{w}) : (tensorDiagram K W).IsLeftAdjoint := by
  have : PreservesColimitsOfSize.{0,w} (tensorDiagram K W) := by
    apply preservesColimits_of_evaluation
    intro k
    change PreservesColimitsOfSize.{0,w} (tensorRight (W.obj k))
    infer_instance
  exact Presheaf.isLeftAdjoint_of_preservesColimits.{w,0,w} (tensorDiagram K W)

lemma simplicialSet_isLocallyPresentable : IsLocallyPresentable.{w} SSet.{w} :=
  SerrePositivity.Smith.AccessibleLimits.functorCategory_isLocallyPresentable
    (C := Type w) SimplexCategoryᵒᵖ


local instance : IsLocallyPresentable.{w} SSet.{w} := simplicialSet_isLocallyPresentable

/-- The weighted cone space is the actual right adjoint of pointwise tensor. -/
def coneSpace (W : K ⥤ SSet.{w}) : (K ⥤ SSet.{w}) ⥤ SSet.{w} :=
  (tensorDiagram K W).rightAdjoint

def adjunction (W : K ⥤ SSet.{w}) : tensorDiagram K W ⊣ coneSpace K W :=
  Adjunction.ofIsLeftAdjoint _

variable [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{w})]

lemma tensorDiagram_isLeftQuillen (W : K ⥤ SSet.{w})
    (hW : let := Projective.modelCategory K I J; IsCofibrant W) :
    let := Projective.modelCategory K I J
    IsLeftQuillen (tensorDiagram K W) := by
  let := Projective.modelCategory K I J
  have : IsCofibrant W := hW
  have := Projective.pointwise_isQuillenBifunctor K I J
    (curriedTensor SSet.{w}) (MonoidalClosed.internalHom (C := SSet.{w}))
    MonoidalClosed.internalHomAdjunction₂
  have : ∀ X : SSet.{w},
      ((pointwise K (curriedTensor SSet.{w})).flip.flip.obj X).IsLeftAdjoint :=
    fun X => ((PointwiseAdjunction.adjunction K
      (MonoidalClosed.internalHomAdjunction₂ (C := SSet.{w}))).adj X).isLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant (pointwise K (curriedTensor SSet.{w})).flip W

lemma coneSpace_isRightQuillen (W : K ⥤ SSet.{w})
    (hW : let := Projective.modelCategory K I J; IsCofibrant W) :
    let := Projective.modelCategory K I J
    IsRightQuillen (coneSpace K W) := by
  let := Projective.modelCategory K I J
  have := tensorDiagram_isLeftQuillen K I J W hW
  exact (isLeftQuillen_iff_isRightQuillen (adjunction K W)).mp inferInstance

end SerrePositivity.DiagramModel.WeightedCones
