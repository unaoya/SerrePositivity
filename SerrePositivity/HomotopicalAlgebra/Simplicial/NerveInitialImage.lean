module

public import SerrePositivity.CategoryTheory.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # An initial object gives a model-free localized contraction of its nerve

The actual map to the terminal simplex has the actual initial vertex as
inverse after every functor inverting anodyne maps.
-/

@[expose] public section
universe u v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.NerveInitialImage
variable {C : Type u} [Category.{v} C] {a : C} (ha : IsInitial a)

def contraction : (Functor.const C).obj a ⟶ 𝟭 C where
  app c := ha.to c
  naturality {_ _} _ := ha.hom_ext _ _

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def terminalImageIso : L.obj (nerve C) ≅
    L.obj (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0)) where
  hom := L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C))
  inv := L.map (NerveHomotopy.point a)
  hom_inv_id := by
    rw [← L.map_comp, NerveHomotopy.constant_eq]
    have h := AnodyneHomotopy.map_homotopy_eq L hL
      (NerveHomotopy.homotopy (contraction ha))
    exact h.trans (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    have h : NerveHomotopy.point a ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve C) = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, L.map_id]

end SerrePositivity.SimplicialModel.NerveInitialImage
