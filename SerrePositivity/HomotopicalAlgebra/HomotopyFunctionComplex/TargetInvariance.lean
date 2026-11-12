module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-! # Target invariance of the resolution Hom

The simplicial model is an explicit parameter, with cofibrations equal to
monomorphisms. No model-existence citation is imported into these proofs.
Boundary lifting proves preservation of trivial fibrations; Brown's lemma
then gives invariance on fibrant targets.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))

include hcof hA in
lemma cosimplicialHom_trivialFibration {Y Z : C} (p : Y ⟶ Z)
    [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := by
  rw [← MorphismProperty.rlp_eq_of_wfs (cofibrations SSet.{v})
    (trivialFibrations SSet.{v}), hcof, SSet.rlp_monomorphisms]
  intro X Y i hi
  obtain ⟨n⟩ := hi
  exact boundary_lifting_of_reedyCofibrant A n hA p

include hcof hA in
lemma cosimplicialHom_weakEquivalence_of_fibrant {Y Z : C}
    [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A
  let h := Classical.choice (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : Fibration h.p := (fibration_iff _).mpr h.hp
  have : WeakEquivalence (F.map h.p) :=
    (weakEquivalence_iff _).mpr (cosimplicialHom_trivialFibration hcof A hA h.p).2
  have : WeakEquivalence (F.map h.r) :=
    (weakEquivalence_iff _).mpr (cosimplicialHom_trivialFibration hcof A hA h.r).2
  have hr : F.map h.i ≫ F.map h.r = 𝟙 _ := by
    rw [← F.map_comp, h.i_r, F.map_id]
  have : WeakEquivalence (F.map h.i) := weakEquivalence_of_postcomp_of_fac hr
  have hf : WeakEquivalence (F.map f) := by
    rw [← h.fac, F.map_comp]
    infer_instance
  exact (weakEquivalence_iff _).mp hf

include hcof hA in
lemma cosimplicialHom_geometricWeakEquivalence_of_fibrant
    (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    SimplicialHomotopy.weakEquivalences ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f) :=
  hw ▸ cosimplicialHom_weakEquivalence_of_fibrant hcof A hA f

include hcof in
lemma chosenResolutionHom_map_target_weakEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} (((chosenResolutionHom cof fib).obj X).map f) := by
  have := fibrantTarget_isFibrant fib Y
  have := fibrantTarget_isFibrant fib Z
  have : WeakEquivalence ((fibrantTarget fib).map f) :=
    (weakEquivalence_iff _).mpr (fibrantTarget_map_weakEquivalence fib f hf)
  exact cosimplicialHom_weakEquivalence_of_fibrant hcof _
    ((cosimplicialResolutionFamily cof).cofibrant X.unop) ((fibrantTarget fib).map f)

end SerrePositivity.HomotopyFunctionComplex
