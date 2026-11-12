module

public import SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrames
public import SerrePositivity.HomotopicalAlgebra.Localization.Basic

/-! # Original locality tests using the natural cofibrant arrow frames

The frame representative of any source arrow gives the same weak-equivalence
test as its original chosen RMap. On fibrant targets, no target replacement
is needed for the test. No localized model structure is assumed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.ArrowFrames
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

abbrev testMap (f : Arrow C) (Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((target cof).obj f)).obj Y ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((source cof).obj f)).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((inclusion cof).app f)).app Y

variable [ModelCategory SSet.{v}]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma projectionHom_weakEquivalence (f : Arrow C) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((projection cof).app f)).app Y) :=
  cosimplicialHomMap_weakEquivalence hcof ((projection cof).app f)
    (target_reedyCofibrant cof f) ((cosimplicialResolutionFamily cof).cofibrant f.right)
    (projection_weakEquivalence cof f) Y

include hcof in
lemma testMap_replaced_iff (f : Arrow C) (Y : C) :
    weakEquivalences SSet.{v} (testMap cof f ((fibrantTarget fib).obj Y)) ↔
      mappingTest cof fib Y f.hom := by
  have := fibrantTarget_isFibrant fib Y
  have hp := projectionHom_weakEquivalence cof hcof f ((fibrantTarget fib).obj Y)
  have hc := congr_app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.map_comp
    ((projection cof).app f).op ((inclusion cof).app f).op) ((fibrantTarget fib).obj Y)
  rw [← op_comp, factorization] at hc
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((projection cof).app f)).app ((fibrantTarget fib).obj Y)) ≫
      testMap cof f ((fibrantTarget fib).obj Y) =
    ((chosenResolutionHom cof fib).map f.hom.op).app Y := hc.symm
  change weakEquivalences SSet.{v} (testMap cof f ((fibrantTarget fib).obj Y)) ↔
    weakEquivalences SSet.{v} (((chosenResolutionHom cof fib).map f.hom.op).app Y)
  constructor
  · intro h
    exact he ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hp h
  · intro h
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hp (he.symm ▸ h)

include hcof in
lemma testMap_weakEquivalence_iff_replaced (f : Arrow C) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} (testMap cof f Y) ↔
      weakEquivalences SSet.{v} (testMap cof f ((fibrantTarget fib).obj Y)) := by
  have := fibrantTarget_isFibrant fib Y
  let q : Y ⟶ (fibrantTarget fib).obj Y := (fibrantTargetComparison fib).app Y
  have : WeakEquivalence q := ⟨fibrantTargetComparison_weakEquivalence fib Y⟩
  have hA := cosimplicialHom_weakEquivalence_of_fibrant hcof ((source cof).obj f)
    (source_reedyCofibrant cof f) q
  have hB := cosimplicialHom_weakEquivalence_of_fibrant hcof ((target cof).obj f)
    (target_reedyCofibrant cof f) q
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((inclusion cof).app f)).naturality q
  constructor
  · intro h
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hB
      (hn.symm ▸ (weakEquivalences SSet.{v}).comp_mem _ _ h hA)
  · intro h
    exact (weakEquivalences SSet.{v}).of_postcomp _ _ hA
      (hn ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hB h)

include hcof in
lemma testMap_iff_of_fibrant (f : Arrow C) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} (testMap cof f Y) ↔ mappingTest cof fib Y f.hom :=
  (testMap_weakEquivalence_iff_replaced cof fib hcof f Y).trans
    (testMap_replaced_iff cof fib hcof f Y)

include hcof in
lemma localObjects_iff_of_fibrant (S : MorphismProperty C) (Y : C) [IsFibrant Y] :
    localObjects cof fib S Y ↔
      ∀ f : Arrow C, S f.hom → weakEquivalences SSet.{v} (testMap cof f Y) := by
  constructor
  · intro h f hf
    exact (testMap_iff_of_fibrant cof fib hcof f Y).mpr (h f.hom hf)
  · intro h X Z f hf
    exact (testMap_iff_of_fibrant cof fib hcof (Arrow.mk f) Y).mp (h (Arrow.mk f) hf)

end SerrePositivity.Bousfield.ArrowFrames
