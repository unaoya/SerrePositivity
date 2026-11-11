module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomConstantWeight
public import SerrePositivity.HomotopicalAlgebra.Diagram.DegreeZeroHomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.EvaluatedFrame

/-! # Actual source comparison from weighted frame realization to hocolim

The comparison uses an augmented weight W, the constant-unit realization
isomorphism and the proved degree-zero hocolim comparison. The only
unproved weak-equivalence step is stated precisely as the image of the
weight augmentation under realization; it is not supplied as an axiom.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.WeightedSourceComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev frames (D : K ⥤ C) := (EvaluatedFrame.family K I J).obj D

/-- Tensoring a weight with the actual simplicial unit gives the same weight. -/
def unitTensorIso (W : Kᵒᵖ ⥤ SSet.{w}) :
    (WeightedCones.tensorDiagram Kᵒᵖ W).obj (𝟙_ SSet.{w}) ≅ W :=
  NatIso.ofComponents (fun k => λ_ (W.obj k)) (by
    intro k l f
    exact leftUnitor_naturality (W.map f))

def constantIso (D : K ⥤ C) :
    (SmallHomFrameWeights.functor K (frames K I J D)).obj
        (ConstantWeightRealization.unitWeight K) ≅
      (DegreeZeroHomotopyColimit.colimitFamily K I J).obj D :=
  SmallHomConstantWeight.unitIso K (frames K I J D)

/-- This entire tail is already a weak equivalence. -/
def tail (D : K ⥤ C) :
    (SmallHomFrameWeights.functor K (frames K I J D)).obj
        (ConstantWeightRealization.unitWeight K) ⟶
      (HomotopyColimit.functor K I J).obj D :=
  (constantIso K I J D).hom ≫ (DegreeZeroHomotopyColimit.comparison K I J).app D

lemma tail_weakEquivalence (D : K ⥤ C) : weakEquivalences C (tail K I J D) :=
  (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso (constantIso K I J D).hom)
    (DegreeZeroHomotopyColimit.comparison_weakEquivalence K I J D)

/-- The actual map from the source of the weighted Quillen adjunction at the
simplicial unit into the specified homotopy colimit. -/
def comparison (D : K ⥤ C) {W : Kᵒᵖ ⥤ SSet.{w}}
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    (SmallHomFrameWeights.weightedFunctor K (frames K I J D) W).obj (𝟙_ SSet.{w}) ⟶
      (HomotopyColimit.functor K I J).obj D :=
  (SmallHomFrameWeights.functor K (frames K I J D)).map (unitTensorIso K W).hom ≫
    (SmallHomFrameWeights.functor K (frames K I J D)).map q ≫ tail K I J D

/-- The source weak-equivalence question is exactly the realization of q.
In particular, no preservation theorem for noncofibrant constant weights
is hidden inside this construction. -/
lemma comparison_weakEquivalence_iff (D : K ⥤ C) {W : Kᵒᵖ ⥤ SSet.{w}}
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    weakEquivalences C (comparison K I J D q) ↔ weakEquivalences C
      ((SmallHomFrameWeights.functor K (frames K I J D)).map q) := by
  let F := SmallHomFrameWeights.functor K (frames K I J D)
  let a := F.map (unitTensorIso K W).hom
  let b := F.map q
  let c := tail K I J D
  have ha : weakEquivalences C a := (weakEquivalences C).of_isIso a
  have hc : weakEquivalences C c := tail_weakEquivalence K I J D
  change weakEquivalences C (a ≫ b ≫ c) ↔ weakEquivalences C b
  constructor
  · intro h
    exact (weakEquivalences C).of_postcomp b c hc
      ((weakEquivalences C).of_precomp a (b ≫ c) ha h)
  · intro h
    exact (weakEquivalences C).comp_mem a (b ≫ c) ha
      ((weakEquivalences C).comp_mem b c h hc)

end SerrePositivity.DiagramModel.WeightedSourceComparison
