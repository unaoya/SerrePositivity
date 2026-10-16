module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace

/-! # Actual resolution maps carried by every higher lift simplex

The full natural transformation is retained, not only its diagonal value.
Its equation over the original base follows from the actual pullback condition.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionLiftRows
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
variable (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {T : SSet.{v}}
  (s : T ⟶ ResolutionLiftSpace.obj X Y f)

def map (n : SimplexCategoryᵒᵖ) (x : T.obj n) : ResolutionFrameRows.row X n.unop ⟶ Y where
  base := f
  diagram := ((s ≫ ResolutionLiftSpace.inclusion X Y f).app n x)
  over := by
    have h := congrArg (fun k => k.app n (s.app n x))
      (LiftSpace.over (ResolutionLiftSpace.frame X).obj (ResolutionLiftSpace.frame X).augmentation
        Y.resolution.augmentation (ResolutionLiftSpace.baseMap X Y f))
    change ((s ≫ ResolutionLiftSpace.inclusion X Y f).app n x) ≫ Y.resolution.augmentation =
      (ResolutionLiftSpace.frame X).augmentation.app n.unop ≫
        (X.resolution.augmentation ≫ (Functor.const SimplexCategory).map f) at h
    change _ = ((ResolutionLiftSpace.frame X).augmentation.app n.unop ≫
      X.resolution.augmentation) ≫ (Functor.const SimplexCategory).map f
    exact h.trans (Category.assoc _ _ _).symm

lemma base (n : SimplexCategoryᵒᵖ) (x : T.obj n) : (map X Y f s n x).base = f := rfl

lemma naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : T.obj n) :
    ResolutionFrameRows.rowMap X θ.unop ≫ map X Y f s n x =
      map X Y f s m (T.map θ x) := by
  apply ResolutionObject.Hom.ext
  · exact Category.id_comp _
  · have h := congrArg (fun k => k x) ((s ≫ ResolutionLiftSpace.inclusion X Y f).naturality θ)
    exact h.symm

lemma parameter {U : SSet.{v}} (i : U ⟶ T) (n : SimplexCategoryᵒᵖ) (x : U.obj n) :
    map X Y f (i ≫ s) n x = map X Y f s n (i.app n x) := rfl

lemma diagram_weakEquivalence (hf : weakEquivalences C f) (n : SimplexCategoryᵒᵖ)
    (x : T.obj n) (k : SimplexCategory) :
    weakEquivalences C ((map X Y f s n x).diagram.app k) :=
  ResolutionObject.diagram_weakEquivalence (map X Y f s n x) hf k

end SerrePositivity.HomotopyFunctionComplex.ResolutionLiftRows
