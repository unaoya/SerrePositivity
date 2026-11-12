module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OppositeIso
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.IsoCat

/-!
概要：終点付加と始点付加の反対圏の比較を、nerve の厳密な同型にする。
方針：既存の比較同値の単位と余単位が対象の等号から来ることを確認する。
規約：任意の小さい圏を扱い、元の関手を変更しない。
使われ方：終点 join の元の余錐写像の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
/-- 概要：終点付加の反対圏と反対圏の始点付加の nerve は同型。
方針：同じ比較同値を厳密化。規約：元の順逆関手。使われ方：終点余錐の反転。 -/
def withTerminalOppositeNerveIso (I : Type u) [Category.{u} I] :
    nerve (WithTerminal I)ᵒᵖ ≅ nerve (WithInitial Iᵒᵖ) := by
  let e := WithTerminal.opEquiv (C := I)
  let e' := e.toIsoCat (fun ⟨x⟩ ↦ by cases x <;> rfl) (fun x ↦ by cases x <;> rfl)
    (fun ⟨x⟩ ↦ by cases x <;> rfl) (fun x ↦ by cases x <;> rfl)
  exact {
    hom := nerveMap e'.functor
    inv := nerveMap e'.inverse
    hom_inv_id := by
      change nerveMap (e'.functor ⋙ e'.inverse) = nerveMap (𝟭 _)
      rw [e'.unit_eq]
    inv_hom_id := by
      change nerveMap (e'.inverse ⋙ e'.functor) = nerveMap (𝟭 _)
      rw [e'.counit_eq] }

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
