module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance

/-! # Source invariance of the cosimplicial resolution Hom

Actual relative latching maps control boundary lifting. The constructed
Reedy model and Brown factorization then give invariance on Reedy cofibrant
cosimplicial objects, without functorial source factorizations.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma cosimplicialHomMap_trivialFibration {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hα : reedyLeft simplex (trivialCofibrations C) α) (target : C) [IsFibrant target] :
    trivialFibrations SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app target) := by
  rw [← MorphismProperty.rlp_eq_of_wfs (cofibrations SSet.{v})
    (trivialFibrations SSet.{v}), hcof, SSet.rlp_monomorphisms]
  intro X Z i hi
  obtain ⟨n⟩ := hi
  have : HasLiftingProperty (relativeLatchingMap simplex (SimplexCategory.mk n) α)
      (terminal.from (C := C) target) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hα _) (mem_fibrations _)
  exact boundary_source_lifting α n

abbrev cosimplicialHomSource (Y : C) : (SimplexCategory ⥤ C)ᵒᵖ ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (evaluation C SSet.{v}).obj Y

include hcof in
lemma cosimplicialHomMap_weakEquivalence {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (hα : ∀ n, weakEquivalences C (α.app n)) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) := by
  let := simplexModelCategory C
  have : IsCofibrant A := ⟨hA⟩
  have : IsCofibrant B := ⟨hB⟩
  have : WeakEquivalence α := ⟨hα⟩
  let h := Classical.choice (inferInstance : Nonempty (CofibrantBrownFactorization α))
  have : Cofibration h.i := (cofibration_iff _).mpr h.hi
  have hi : reedyLeft simplex (trivialCofibrations C) h.i :=
    (reedyLeft_trivialCofibrations_iff simplex h.i).mpr
      ⟨h.hi, (mem_weakEquivalences h.i)⟩
  have hs : reedyLeft simplex (trivialCofibrations C) h.s :=
    (reedyLeft_trivialCofibrations_iff simplex h.s).mpr
      ⟨mem_cofibrations h.s, mem_weakEquivalences h.s⟩
  let F := cosimplicialHomSource Y
  have hi' : weakEquivalences SSet.{v} (F.map (Quiver.Hom.op h.i)) :=
    (cosimplicialHomMap_trivialFibration hcof h.i hi Y).2
  have hs' : weakEquivalences SSet.{v} (F.map (Quiver.Hom.op h.s)) :=
    (cosimplicialHomMap_trivialFibration hcof h.s hs Y).2
  have he : F.map (Quiver.Hom.op h.p) ≫ F.map (Quiver.Hom.op h.s) = 𝟙 _ := by
    rw [← F.map_comp]
    change F.map (Quiver.Hom.op (h.s ≫ h.p)) = _
    rw [h.s_p]
    exact F.map_id _
  have hp : weakEquivalences SSet.{v} (F.map (Quiver.Hom.op h.p)) :=
    (weakEquivalences SSet.{v}).of_postcomp _ _ hs'
      (he.symm ▸ (weakEquivalences SSet.{v}).id_mem _)
  have hf : F.map (Quiver.Hom.op h.p) ≫ F.map (Quiver.Hom.op h.i) =
      F.map (Quiver.Hom.op α) := by
    rw [← F.map_comp]
    exact congrArg F.map (congrArg Quiver.Hom.op h.fac)
  have res : weakEquivalences SSet.{v} (F.map (Quiver.Hom.op α)) :=
    hf ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hp hi'
  exact res

include hcof in
lemma cosimplicialHomMap_geometricWeakEquivalence
    (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
    {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (hα : ∀ n, weakEquivalences C (α.app n)) (Y : C) [IsFibrant Y] :
    SimplicialHomotopy.weakEquivalences ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) :=
  hw ▸ cosimplicialHomMap_weakEquivalence hcof α hA hB hα Y

include hcof in
lemma chosenResolutionHom_map_source_weakEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X Z : Cᵒᵖ} (f : X ⟶ Z) (hf : weakEquivalences C f.unop) (Y : C) :
    weakEquivalences SSet.{v} (((chosenResolutionHom cof fib).map f).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact cosimplicialHomMap_weakEquivalence hcof
    ((cosimplicialResolutionFamily cof).obj.map f.unop)
    ((cosimplicialResolutionFamily cof).cofibrant Z.unop)
    ((cosimplicialResolutionFamily cof).cofibrant X.unop)
    ((cosimplicialResolutionFamily cof).map_weakEquivalence f.unop hf) _

include hcof in
lemma chosenResolutionHom_map_both_weakEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    weakEquivalences SSet.{v}
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (chosenResolutionHom_map_source_weakEquivalence hcof cof fib f hf Y)
    (chosenResolutionHom_map_target_weakEquivalence hcof cof fib X' g hg)

include hcof in
lemma chosenResolutionHom_map_both_geometricWeakEquivalence
    (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    SimplicialHomotopy.weakEquivalences
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) :=
  hw ▸ chosenResolutionHom_map_both_weakEquivalence hcof cof fib f hf g hg

end SerrePositivity.HomotopyFunctionComplex
