module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCommaLowerIso

/-!
概要：指定同型の逆との型付き一致から、元の合成の等号同型性を得る。
方針：元の端点等号と指定値の一致を消去し、逆同型を相殺する。
規約：HEq から端点等号を推測せず、明示した等号を使う。
使われ方：旧族での往復した指定変換の相殺。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の同じ指定同型の逆との合成は等号同型。
方針：明示した端点等号で消去。規約：指定値を保持。使われ方：相対比較の往復。 -/
lemma isFunctorEqIso_trans_of_inverse_heq {A B : SSet.{u}} {f g h : A ⟶ B}
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (hf : f = h) (hr : HEq l.symm r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (l ≪≫ r) := by
  subst h
  cases eq_of_heq hr
  exact ⟨rfl, by change _ = Iso.refl _; simp⟩
/-- 概要：明示した端点表示で元の指定同型と逆に一致する二同型は相殺する。
方針：端点と指定値の等号を消去。規約：全指定値。使われ方：表示変更後の往復。 -/
lemma isFunctorEqIso_trans_of_inverse_pair_heq {A B : SSet.{u}}
    {a b c x y : A ⟶ B} (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso x y)
    (ha : a = y) (hb : b = x) (hc : c = y) (hl : HEq l d.symm) (hr : HEq r d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (l ≪≫ r) := by
  subst a b c
  cases eq_of_heq hl
  cases eq_of_heq hr
  exact ⟨rfl, by change _ = Iso.refl _; simp⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
