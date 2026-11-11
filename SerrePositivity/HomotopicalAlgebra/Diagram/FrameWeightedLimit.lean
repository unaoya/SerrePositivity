module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomFrameWeights
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit

/-! # Weighted frame Hom computes the actual simplicial homotopy limit

The weight is the specified projective cofibrant replacement of the
constant unit diagram. Weighted frame Hom is the right adjoint of an
actual left Quillen realization. On fibrant targets it maps naturally by
a weak equivalence to the existing homotopy limit of the pointwise
small-Hom diagram. Source identification with hocolim is not asserted here.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.FrameWeightedLimit
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

abbrev functor (A : K ⥤ SimplexCategory ⥤ C) : C ⥤ SSet.{w} :=
  SmallHomFrameWeights.hom K A ⋙ HomotopyLimit.functor Kᵒᵖ I J

abbrev weightedHom (A : K ⥤ SimplexCategory ⥤ C) : C ⥤ SSet.{w} :=
  SmallHomFrameWeights.weightedHom K A (HomotopyCones.weight Kᵒᵖ I J)

abbrev weightedFunctor (A : K ⥤ SimplexCategory ⥤ C) : SSet.{w} ⥤ C :=
  SmallHomFrameWeights.weightedFunctor K A (HomotopyCones.weight Kᵒᵖ I J)

def adjunction (A : K ⥤ SimplexCategory ⥤ C) : weightedFunctor K I J A ⊣ weightedHom K I J A :=
  SmallHomFrameWeights.weightedAdjunction K A (HomotopyCones.weight Kᵒᵖ I J)

def comparison (A : K ⥤ SimplexCategory ⥤ C) : weightedHom K I J A ⟶ functor K I J A :=
  Functor.whiskerLeft (SmallHomFrameWeights.hom K A) (HomotopyCones.comparison Kᵒᵖ I J)

variable
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

include hcof hfib hA hconst

lemma weighted_isLeftQuillen : IsLeftQuillen (weightedFunctor K I J A) :=
  SmallHomFrameWeights.weighted_isLeftQuillen K I J hcof hfib A hA hconst _
    (HomotopyCones.weight_isCofibrant Kᵒᵖ I J)

lemma weighted_isRightQuillen : IsRightQuillen (weightedHom K I J A) := by
  have := weighted_isLeftQuillen K I J hcof hfib A hA hconst
  exact (isLeftQuillen_iff_isRightQuillen (adjunction K I J A)).mp inferInstance

lemma hom_isFibrant (Y : C) [IsFibrant Y] :
    let := Projective.modelCategory Kᵒᵖ I J
    IsFibrant ((SmallHomFrameWeights.hom K A).obj Y) := by
  let := Projective.modelCategory Kᵒᵖ I J
  let R := SmallHomFrameWeights.hom K A
  have : R.IsRightAdjoint := (SmallHomFrameWeights.adjunction K A).isRightAdjoint
  have : IsRightQuillen R := SmallHomFrameWeights.isRightQuillen K I J hcof hfib A hA hconst
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from Y))
    (terminalIsTerminal.isTerminalObj R (⊤_ C))).mpr (Quillen.map_fibration R (terminal.from Y))

lemma comparison_weakEquivalence (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{w} ((comparison K I J A).app Y) := by
  have : IsQuillenBifunctor (curriedTensor SSet.{w}) :=
    SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyCones.comparison_weakEquivalence_of_fibrant Kᵒᵖ I J
    ((SmallHomFrameWeights.hom K A).obj Y) (hom_isFibrant K I J hcof hfib A hA hconst Y)

/-- After an explicit source fibrant replacement, the comparison is a weak
 equivalence at every original target, still as an actual natural transformation. -/
lemma replacedComparison_weakEquivalence
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (Y : C) : weakEquivalences SSet.{w}
      ((Functor.whiskerLeft (fibrantTarget fib) (comparison K I J A)).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact comparison_weakEquivalence K I J hcof hfib A hA hconst ((fibrantTarget fib).obj Y)

end SerrePositivity.DiagramModel.FrameWeightedLimit
