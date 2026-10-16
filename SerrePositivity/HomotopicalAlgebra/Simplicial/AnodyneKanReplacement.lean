module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # A value-side Kan replacement from the horn small-object argument alone

The chosen factorization and its unit are actual functorial data. No
model structure, weak-equivalence class, or source replacement is assumed.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.AnodyneKanReplacement

def factorization : MorphismProperty.FunctorialFactorizationData
    SSet.anodyneExtensions.{v} SSet.modelCategoryQuillen.J.rlp := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact MorphismProperty.functorialFactorizationData _ _

def terminalArrows : SSet.{v} ⥤ Arrow SSet.{v} where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (by simp)

abbrev functor : SSet.{v} ⥤ SSet.{v} := terminalArrows ⋙ factorization.Z

def unit : 𝟭 SSet.{v} ⟶ functor where
  app X := factorization.i.app (Arrow.mk (terminal.from X))
  naturality {_ _} f := factorization.i.naturality (terminalArrows.map f)

lemma unit_anodyne (X : SSet.{v}) : SSet.anodyneExtensions ((unit.{v}).app X) :=
  factorization.hi _

lemma terminal_rlp (X : SSet.{v}) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor.{v}).obj X)) := by
  have h := factorization.hp (Arrow.mk (terminal.from X))
  have he : terminal.from (functor.obj X) =
      factorization.p.app (Arrow.mk (terminal.from X)) := terminal.hom_ext _ _
  rw [he]
  exact h

end SerrePositivity.SimplicialModel.AnodyneKanReplacement
