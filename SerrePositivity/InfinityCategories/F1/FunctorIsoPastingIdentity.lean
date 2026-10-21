module

public import SerrePositivity.InfinityCategories.F1.FunctorIsoPastingTransport

/-!
概要：端点の表示を含めた、指定関手同型の二因子の貼り合わせ等式。
方針：同じ指定値の貼り合わせを命題に包み、終辺の同じ値への移送を保存する。
規約：等式の内容と元の同型の指定値を保持する。
使われ方：大きな大域 Hom 上の三角等式を一般の貼り合わせ則から検証する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 二因子の指定合成は、端点の表示を除いて指定された終辺と同じ値。 -/
def FunctorIsoPastingHEq {X Y : SSet.{u}} {a b c a' c' : X ⟶ Y}
    (e : FunctorIso a b) (d : FunctorIso b c) (n : FunctorIso a' c') : Prop :=
  HEq (e ≪≫ d) n

/-- 元の貼り合わせ等式の終辺を、その同じ指定値で置き換えられる。 -/
lemma functorIsoPastingHEq_of_eq_of_heq {X Y : SSet.{u}} {a b c a' c' : X ⟶ Y}
    (e : FunctorIso a b) (d : FunctorIso b c) (m : FunctorIso a c)
    (n : FunctorIso a' c') (h : e ≪≫ d = m) (hn : HEq n m) :
    FunctorIsoPastingHEq e d n := by
  exact HEq.trans (heq_of_eq h) hn.symm

end SerrePositivity.InfinityCategories
