module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingTransport

/-!
概要：対象の等式で端点をそろえ、同じ指定同型の貼り合わせを回収する。
方針：ホモトピー圏の対象の等式を消去して指定値の同じ合成を使う。
規約：元の同型の値を変更しない。
使われ方：大きな関手の射を逆算せずに、指定された局所自然性の合成を検証する。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 対象と指定値の一致を保って、同じ二同型の貼り合わせを回収する。 -/
lemma iso_pasting_heq_of_endpoint_eq {C : Type u} [Category.{v} C]
    {a b c a' b' c' : C} (e : a ≅ b) (d : b ≅ c) (E : a' ≅ b') (N : b' ≅ c')
    (ha : a = a') (hb : b = b') (hc : c = c')
    (he : HEq E e) (hd : HEq N d) : HEq (e ≪≫ d) (E ≪≫ N) := by
  subst a' b' c'
  cases eq_of_heq he
  cases eq_of_heq hd
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
