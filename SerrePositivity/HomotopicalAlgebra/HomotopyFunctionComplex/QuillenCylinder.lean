module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame

public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCylinder

/-! # The actual standard interval under a left Quillen functor is a good cylinder

The cylinder, both endpoint maps and the projection are the actual images
of Δ[1], its two cofaces and its codegeneracy. Cofibrancy of the boundary
comes from the standard Reedy frame, not an assumed cylinder axiom for the
target tensor action. Source and target Hom universes are independent.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame
variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasFiniteColimits C]
  [ModelCategory SSet.{w}]
  (L : SSet.{w} ⥤ C) [L.IsLeftAdjoint] [Quillen.IsLeftQuillen L]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

omit [L.IsLeftAdjoint] [HasFiniteColimits C] in
include hcof hw in
lemma standardMap_weakEquivalence {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (L.map (SSet.stdSimplex.map f)) := by
  have hn : IsCofibrant (SSet.stdSimplex.{w}.obj n) := by
    constructor
    rw [hcof]
    infer_instance
  have hm : IsCofibrant (SSet.stdSimplex.{w}.obj m) := by
    constructor
    rw [hcof]
    infer_instance
  have : WeakEquivalence (SSet.stdSimplex.{w}.map f) :=
    ⟨hw.symm ▸ SimplicialHomotopy.stdSimplex_map_weakEquivalence f⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L _)

def cylinder : Cylinder (L.obj (SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0))) :=
  cosimplicialCylinder (SSet.stdSimplex ⋙ L) (standardMap_weakEquivalence L hcof hw)

lemma cylinder_isGood : (cylinder L hcof hw).IsGood :=
  cosimplicialCylinder_isGood (SSet.stdSimplex ⋙ L) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame.reedyCofibrant L hcof)
    (standardMap_weakEquivalence L hcof hw)

end SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame

namespace SerrePositivity.ModelCylinder
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasBinaryCoproducts C] {A B : C}

def changeBase (P : Cylinder A) (e : A ≅ B) : Cylinder B where
  I := P.I
  i₀ := e.inv ≫ P.i₀
  i₁ := e.inv ≫ P.i₁
  π := P.π ≫ e.hom
  i₀_π := by simp [Category.assoc]
  i₁_π := by simp [Category.assoc]
  weakEquivalence_π := by infer_instance

lemma changeBase_isGood (P : Cylinder A) [P.IsGood] (e : A ≅ B) :
    (changeBase P e).IsGood := by
  have h : coprod.map e.inv e.inv ≫ P.i = (changeBase P e).i := by
    ext <;> simp [Precylinder.i, changeBase]
  exact ⟨h ▸ (inferInstance : Cofibration (coprod.map e.inv e.inv ≫ P.i))⟩

end SerrePositivity.ModelCylinder
