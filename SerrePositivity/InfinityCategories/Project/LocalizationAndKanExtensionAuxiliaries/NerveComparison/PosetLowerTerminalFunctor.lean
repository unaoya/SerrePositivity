module

public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：厳密下方集合に終点を加えた圏は、元の弱下方集合と厳密に同型。
方針：元の包含と指定点で関手を作り、全射上の全単射と対象の全単射を証明する。
規約：順序集合の有限性や元の点の極大性を仮定しない。
使われ方：有限半順序形状の点追加を余錐形状として表示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
/-- 概要：厳密下方集合の元と新しい終点を、元の弱下方集合へ送る。
方針：包含の終点拡張。規約：新しい終点は指定点 a。使われ方：下方形状の同定。 -/
def posetLowerTerminalFunctor {P : Type u} [PartialOrder P] (a : P) :
    WithTerminal {p : P // p < a} ⥤ {p : P // p ≤ a} :=
  WithTerminal.lift (Z := ⟨a, le_rfl⟩)
    (⟨fun b ↦ ⟨b.val, b.property.le⟩, fun _ _ h ↦ h⟩ :
      {p : P // p < a} →o {p : P // p ≤ a}).toFunctor
    (fun b ↦ homOfLE b.property.le) (fun _ _ _ ↦ Subsingleton.elim _ _)
/-- 概要：元の下方包含と指定点による関手そのものは圏の同型。
方針：充満忠実性と対象の全単射。規約：元の順射。使われ方：nerve の実同型。 -/
instance posetLowerTerminalFunctor_isIso {P : Type u} [PartialOrder P] (a : P) :
    (posetLowerTerminalFunctor a).IsIso := by
  classical
  refine { faithful := ?_, full := ?_, bijective_obj := ?_ }
  · constructor
    intro x y f g h
    cases x with
    | of x =>
      cases y with
      | of y => exact Subsingleton.elim (WithTerminal.down f) (WithTerminal.down g)
      | star => exact Subsingleton.elim (show PUnit from f) (show PUnit from g)
    | star =>
      cases y with
      | of y => exact PEmpty.elim f
      | star => exact Subsingleton.elim (show PUnit from f) (show PUnit from g)
  · constructor
    intro x y f
    cases x with
    | of x =>
      cases y with
      | of y => exact ⟨homOfLE (leOfHom f), Subsingleton.elim _ _⟩
      | star => exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
    | star =>
      cases y with
      | of y => exact False.elim (not_lt_of_ge (leOfHom f) y.property)
      | star => exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
  · constructor
    · intro x y h
      cases x with
      | of x =>
        cases y with
        | of y =>
          exact congrArg WithTerminal.of
            (Subtype.ext (congrArg (fun b : {p : P // p ≤ a} ↦ b.val) h))
        | star =>
          exact False.elim (x.property.ne (congrArg (fun b : {p : P // p ≤ a} ↦ b.val) h))
      | star =>
        cases y with
        | of y =>
          exact False.elim
            (y.property.ne (congrArg (fun b : {p : P // p ≤ a} ↦ b.val) h).symm)
        | star => rfl
    · intro b
      by_cases h : b.val = a
      · exact ⟨WithTerminal.star, Subtype.ext h.symm⟩
      · exact ⟨WithTerminal.of ⟨b.val, lt_of_le_of_ne b.property h⟩, rfl⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
