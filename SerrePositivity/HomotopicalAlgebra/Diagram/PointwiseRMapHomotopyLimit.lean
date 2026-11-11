module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallPointwiseMappingComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimWeightedComparison

/-! # Homotopy limits of pointwise chosen small-Hom RMap

Apply the actual homotopical holim functor to the two-variable natural
pointwise comparison cospan. The right endpoint is exactly the holim of
the diagram k ↦ the specified small-Hom RMap(D(k),Y).
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.PointwiseRMapHomotopyLimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev functor : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  SmallPointwiseMappingComparison.pointwiseRMap K cof fib ⋙
    (Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj (HomotopyLimit.functor Kᵒᵖ IS JS)

abbrev middle : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  SmallPointwiseMappingComparison.middle K I J cof fib ⋙
    (Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj (HomotopyLimit.functor Kᵒᵖ IS JS)

abbrev left : functor K IS JS cof fib ⟶ middle K I J IS JS cof fib :=
  Functor.whiskerRight (SmallPointwiseMappingComparison.left K I J cof fib)
    ((Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj (HomotopyLimit.functor Kᵒᵖ IS JS))

abbrev right : HocolimWeightedComparison.holim K I J IS JS fib ⟶ middle K I J IS JS cof fib :=
  Functor.whiskerRight (SmallPointwiseMappingComparison.right K I J cof fib)
    ((Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj (HomotopyLimit.functor Kᵒᵖ IS JS))

variable (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

include hcof hfib in
lemma left_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((left K I J IS JS cof fib).app D).app Y) := by
  have := SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyLimit.map_weakEquivalence Kᵒᵖ IS JS
    (((SmallPointwiseMappingComparison.left K I J cof fib).app D).app Y)
    (SmallPointwiseMappingComparison.left_weakEquivalence K I J cof fib hcof D Y)

include hcof hfib in
lemma right_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((right K I J IS JS cof fib).app D).app Y) := by
  have := SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  exact HomotopyLimit.map_weakEquivalence Kᵒᵖ IS JS
    (((SmallPointwiseMappingComparison.right K I J cof fib).app D).app Y)
    (SmallPointwiseMappingComparison.right_weakEquivalence K I J cof fib hcof D Y)

end SerrePositivity.DiagramModel.PointwiseRMapHomotopyLimit
