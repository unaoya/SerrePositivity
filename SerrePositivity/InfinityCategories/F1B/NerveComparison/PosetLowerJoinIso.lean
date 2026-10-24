module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.PosetLowerTerminalFunctor
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.TerminalJoinNerveIso

/-!
概要：弱下方集合の nerve を、厳密下方集合の nerve への終点余錐と同定する。
方針：元の終点付加写像と、弱下方集合への圏の厳密な同型を合成する。
規約：元の下方包含と指定点を全単体写像の等号で回収する。
使われ方：点追加の相対補間で、元の試験族を保つ境界の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B
/-- 概要：終点付加した厳密下方集合から弱下方集合への nerve の同型。
方針：元の関手の可逆性。規約：元の順射。使われ方：点追加の形状比較。 -/
def posetLowerTerminalNerveIso {P : Type u} [PartialOrder P] (a : P) :
    nerve (WithTerminal {p : P // p < a}) ≅ nerve {p : P // p ≤ a} := by
  let e := (posetLowerTerminalFunctor a).asIsomorphism
  exact {
    hom := nerveMap e.functor
    inv := nerveMap e.inverse
    hom_inv_id := by
      change nerveMap (e.functor ⋙ e.inverse) = nerveMap (𝟭 _)
      rw [e.unit_eq]
    inv_hom_id := by
      change nerveMap (e.inverse ⋙ e.functor) = nerveMap (𝟭 _)
      rw [e.counit_eq] }
/-- 概要：厳密下方集合と点の join から元の弱下方集合の nerve への同型。
方針：元の関手の可逆性。規約：元の順射。使われ方：点追加の形状比較。 -/
def posetLowerJoinIso {P : Type u} [PartialOrder P] (a : P) :
    join (nerve {p : P // p < a}) (Δ[0] : SSet.{u}) ≅ nerve {p : P // p ≤ a} :=
  terminalJoinNerveIso _ ≪≫ posetLowerTerminalNerveIso a
/-- 概要：元の厳密下方集合の包含を回収する。
方針：終点 join の境界公式。規約：全射の等号。使われ方：相対補間の境界。 -/
lemma posetLowerJoinIso_inl {P : Type u} [PartialOrder P] (a : P) :
    joinInl _ _ ≫ (posetLowerJoinIso a).hom =
      nerveMap (⟨fun b ↦ ⟨b.val, b.property.le⟩, fun _ _ h ↦ h⟩ :
        {p : P // p < a} →o {p : P // p ≤ a}).toFunctor := by
  rw [posetLowerJoinIso, Iso.trans_hom, ← Category.assoc, joinInl_terminalJoinNerveIso]
  rfl
/-- 概要：点側の包含は元の指定点である。
方針：終点 join の境界公式。規約：全射の等号。使われ方：相対補間の境界。 -/
lemma posetLowerJoinIso_inr {P : Type u} [PartialOrder P] (a : P) :
    joinInr _ _ ≫ (posetLowerJoinIso a).hom = nervePoint (⟨a, le_rfl⟩ : {p : P // p ≤ a}) := by
  rw [posetLowerJoinIso, Iso.trans_hom, ← Category.assoc, joinInr_terminalJoinNerveIso]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F1B
