module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimRMapFormula
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-! # Covariant RMap tests extend across actual homotopy colimits

The natural formula proves that a target map passing every pointwise
RMap test also passes the test at the actual hocolim. A weak comparison
from that hocolim to another source transports the conclusion further.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel

namespace SerrePositivity.Bousfield.HomotopyGenerators
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include IS JS hcof hfib hw in
lemma map_at_hocolim_weakEquivalence (D : K ⥤ C) {Y Z : C} (f : Y ⟶ Z)
    (hf : ∀ k, weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op (D.obj k))).map f)) :
    weakEquivalences SSet.{w} (((SmallHomComparison.chosenHom cof fib).obj
      (Opposite.op ((HomotopyColimit.functor K I J).obj D))).map f) := by
  have := SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  let L := (weakEquivalences SSet.{w}).Q
  let e := (HocolimRMapFormula.localizedIso K I J IS JS cof fib hcof hfib hw L).app (Opposite.op D)
  have ht : weakEquivalences SSet.{w}
      (((HocolimRMapFormula.target K IS JS cof fib).obj (Opposite.op D)).map f) :=
    HomotopyLimit.map_weakEquivalence Kᵒᵖ IS JS
      (((SmallPointwiseMappingComparison.pointwiseRMap K cof fib).obj (Opposite.op D)).map f)
      (fun k => hf k.unop)
  have : IsIso (L.map (((HocolimRMapFormula.target K IS JS cof fib).obj
      (Opposite.op D)).map f)) := Localization.inverts L (weakEquivalences SSet.{w}) _ ht
  have hn : L.map (((SmallHomComparison.chosenHom cof fib).obj
      (Opposite.op ((HomotopyColimit.functor K I J).obj D))).map f) ≫ (e.app Z).hom =
    (e.app Y).hom ≫ L.map (((HocolimRMapFormula.target K IS JS cof fib).obj
      (Opposite.op D)).map f) := e.hom.naturality f
  apply (Quillen.weakEquivalences_iff_isIso_map L _).mpr
  apply (isIso_comp_right_iff _ (e.app Z).hom).mp
  rw [hn]
  infer_instance

include hcof in
lemma map_at_source_of_weakComparison {A B Y Z : C} (a : A ⟶ B)
    (ha : weakEquivalences C a) (f : Y ⟶ Z)
    (hf : weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op A)).map f)) :
    weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op B)).map f) := by
  let t := (SmallHomComparison.chosenHom cof fib).map a.op
  have hY := SmallHomComparison.chosenHom_map_source_weakEquivalence hcof cof fib a.op ha Y
  have hZ := SmallHomComparison.chosenHom_map_source_weakEquivalence hcof cof fib a.op ha Z
  exact (weakEquivalences SSet.{w}).of_postcomp _ _ hZ
    ((t.naturality f).symm ▸ (weakEquivalences SSet.{w}).comp_mem _ _ hY hf)

end SerrePositivity.Bousfield.HomotopyGenerators
