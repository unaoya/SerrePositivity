module

public import SerrePositivity.CategoryTheory.Enriched.TensorUnit
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorConstant

/-! # The natural augmentation of the actual simplicial tensor diagram

The tensor of the terminal standard zero-simplex is naturally the original
object, by represented tensor-unit compatibility. The collapse to that
zero-simplex supplies an actual augmentation natural in the source object.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)

abbrev simplexZeroTensorIso : S.tensor.obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ≅ 𝟭 C :=
  S.tensor.mapIso (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ S.unitIso

abbrev simplexCollapse (n : SimplexCategory) : n ⟶ SimplexCategory.mk 0 :=
  SimplexCategory.const n (SimplexCategory.mk 0) 0

lemma simplexCollapse_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    f ≫ simplexCollapse m = simplexCollapse n := by
  ext i
  rfl

def tensorAugmentationAt (X : C) :
    (tensorCosimplicialFamily S).obj X ⟶ (Functor.const SimplexCategory).obj X where
  app n := ((tensorCosimplicialFamily S).obj X).map (simplexCollapse n) ≫
    (simplexZeroTensorIso S).hom.app X
  naturality n m f := by
    let A := (tensorCosimplicialFamily S).obj X
    have h : A.map f ≫ A.map (simplexCollapse m) = A.map (simplexCollapse n) :=
      (A.map_comp _ _).symm.trans (congrArg A.map (simplexCollapse_naturality f))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ (simplexZeroTensorIso S).hom.app X) h).trans
        (Category.comp_id _).symm)

def tensorAugmentation : tensorCosimplicialFamily S ⟶ Functor.const SimplexCategory where
  app X := tensorAugmentationAt S X
  naturality {_ _} f := by
    apply NatTrans.ext
    funext n
    have h := (S.tensor.map (SSet.stdSimplex.map (simplexCollapse n))).naturality f
    have hu := (simplexZeroTensorIso S).hom.naturality f
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ (simplexZeroTensorIso S).hom.app _) h).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k ↦ (S.tensor.map (SSet.stdSimplex.map (simplexCollapse n))).app _ ≫ k)
            hu).trans (Category.assoc _ _ _).symm)))

variable [ModelCategory C] [ModelCategory SSet.{v}]
  [SerrePositivity.Quillen.IsQuillenBifunctor S.tensor]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)

include hcof hw in
lemma tensorAugmentation_weakEquivalence (X : C) [IsCofibrant X] (n : SimplexCategory) :
    weakEquivalences C (((tensorAugmentation S).app X).app n) :=
  (weakEquivalences C).comp_mem _ _
    (tensorCosimplicial_homotopicallyConstant hcof hw S X (simplexCollapse n))
    ((weakEquivalences C).of_isIso ((simplexZeroTensorIso S).hom.app X))

end SerrePositivity.HomotopyFunctionComplex
