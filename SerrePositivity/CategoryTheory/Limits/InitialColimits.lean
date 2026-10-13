module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # 始対象の図式の余極限

各対象が始対象である図式の余極限も始対象となる。
図式の添字圏は空でもよく、基礎圏の始対象の選択を仮定しない。
-/

@[expose] public section

universe v u w w'

noncomputable section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J]

/-- 各対象が始対象である図式の余極限は始対象。 -/
def colimitOfInitialsIsInitial (F : J ⥤ C) [HasColimit F]
    (h : ∀ j, IsInitial (F.obj j)) : IsInitial (colimit F) := by
  let c (Y : C) : Cocone F := {
    pt := Y
    ι.app j := (h j).to Y
    ι.naturality i j f := (h i).hom_ext _ _ }
  apply IsInitial.ofUniqueHom (fun Y => colimit.desc F (c Y))
  intro Y f
  apply colimit.hom_ext
  intro j
  exact (h j).hom_ext _ _

end SerrePositivity
