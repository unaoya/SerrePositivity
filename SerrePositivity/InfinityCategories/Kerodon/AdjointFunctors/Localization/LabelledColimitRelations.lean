module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber

/-!
# 元の余極限の同値関係を値の fiber へ持ち上げる

概要：同じ値を持つ元の代表間の EqvGen は元の fiber の代表間でも成立する。
方針：生成関係・反転・連鎖ごとにラベルの不変性を使う。
規約：元の EqvGen の有限鎖を保持し、共通上界を仮定しない。
使われ方：元の余極限の fiber 比較の単射性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt)

lemma fiber_rel {p q : Σ i, F.obj i} (h : F.ColimitTypeRel p q)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalLabel c p = β) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalLabel c q = β) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ColimitTypeRel (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalFiber c β p hp) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalFiber c β q hq) := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  obtain ⟨f, hf⟩ := h
  exact ⟨f, Subtype.ext hf⟩

lemma fiber_eqvGen {p q : Σ i, F.obj i} (h : Relation.EqvGen F.ColimitTypeRel p q) :
    ∀ (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalLabel c p = β) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalLabel c q = β),
      Relation.EqvGen (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ColimitTypeRel
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalFiber c β p hp) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalFiber c β q hq) := by
  induction h with
  | rel p q h => exact fun hp hq => .rel _ _ (fiber_rel c β h hp hq)
  | refl p => exact fun hp hq => .refl _
  | symm p q h ih => exact fun hp hq => .symm _ _ (ih hq hp)
  | trans p q r hp hq ihp ihq =>
    intro hβp hβr
    have hβq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.totalLabel c q = β := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.label_eqvGen c hp).symm.trans hβp
    exact .trans _ _ _ (ihp hβp hβq) (ihq hβq hβr)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
