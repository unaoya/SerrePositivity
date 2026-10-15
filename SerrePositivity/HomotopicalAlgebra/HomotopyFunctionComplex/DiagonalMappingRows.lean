module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance

/-! # Rowwise comparisons for a double resolution mapping object

The augmented bisimplicial mapping object has actual weak equivalences in
every row. This is not yet a diagonal weak equivalence theorem.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows
variable {C : Type u} [Category.{v} C]

abbrev obj (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (Z : C) :
    SimplexCategoryᵒᵖ ⥤ SSet.{v} := A.op ⋙ cosimplicialHomSource Z

/-- The constant original mapping space maps naturally to all outer rows. -/
def comparison {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C) :
    (Functor.const SimplexCategoryᵒᵖ).obj ((cosimplicialHom B).obj Z) ⟶ obj A Z where
  app n := (cosimplicialHomMap (a.app n.unop)).app Z
  naturality {n m} f := by
    ext k h
    change (a.app m.unop).app k.unop ≫ h =
      (A.map f.unop).app k.unop ≫ ((a.app n.unop).app k.unop ≫ h)
    have he := congr_app (a.naturality f.unop) k.unop
    change (A.map f.unop).app k.unop ≫ (a.app n.unop).app k.unop =
      (a.app m.unop).app k.unop ≫ 𝟙 _ at he
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ h) (he.trans (Category.comp_id _)))).symm

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C
variable {B : SimplexCategory ⥤ C} (q : CofibrantResolution simplex B)

lemma row_cofibrant (n : SimplexCategory) :
    reedyLeft simplex (cofibrations C) (initial.to (q.obj.obj n)) := by
  exact (q.isCofibrant_obj n).mem

lemma row_homotopicallyConstant
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((q.obj.obj k).map f) := by
  have he := (q.augmentation.app k).naturality f
  exact (weakEquivalences C).of_postcomp _ _
    (q.augmentation_weakEquivalence k m)
    (he.symm ▸ (weakEquivalences C).comp_mem _ _
      (q.augmentation_weakEquivalence k n) (hB f))

lemma row_kanComplex
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (n : SimplexCategoryᵒᵖ) (Z : C) [IsFibrant Z] :
    SSet.KanComplex ((obj q.obj Z).obj n) :=
  cosimplicialHom_kanComplex _ (row_cofibrant q n.unop)
    (row_homotopicallyConstant q hB n.unop) Z

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma comparison_weakEquivalence
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (Z : C) [IsFibrant Z] (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((comparison q.augmentation Z).app n) :=
  cosimplicialHomMap_weakEquivalence hcof (q.augmentation.app n.unop)
    (row_cofibrant q n.unop) hB (q.augmentation_weakEquivalence n.unop) Z

end SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows
