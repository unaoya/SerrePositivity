module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の反転を二度適用した関手を恒等関手と厳密に同定する。
方針：標準の二重反転同型の成分が恒等写像であることから関手の外延性を使う。
規約：この等式を一般の圏の同値から推論せず、反転の具体的な成分を計算する。
使われ方：反転した Kan 存在定理を元の三つの単体集合と射へ戻す。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：単体集合の二重反転は元の単体集合に等しい。
方針：二重反転同型の各次数の成分は恒等写像なので、関手の外延性を使う。
規約：証明による型の移送は後続で明示する。
使われ方：二重反転した宇宙と添字の厳密な正規化。 -/
lemma opposite_opposite_eq (X : SSet.{u}) : X.op.op = X := by
  exact Functor.ext_of_iso (SSet.opFunctorCompOpFunctorIso.app X)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- 概要：二重反転同型は単体集合の外延的な等式による射に一致する。
方針：自然変換の各次数で、両辺が恒等写像であることを計算する。
規約：同型の射を一般に eqToHom と同一視する主張ではない。
使われ方：反転関手全体の外延性。 -/
lemma opposite_doubleIso_eqToHom (X : SSet.{u}) :
    (SSet.opFunctorCompOpFunctorIso.app X).hom = eqToHom (opposite_opposite_eq X) := by
  apply NatTrans.ext
  funext n
  rw [eqToHom_app]
  rfl

/-- 概要：反転関手を二度合成すると恒等関手に等しい。
方針：対象の外延的な等式と標準同型の成分の計算をまとめる。
規約：射と対象を同時に正規化するための関手の等式。
使われ方：点ごとの右 Kan 存在条件と構成結果の二重反転を消す。 -/
@[kerodon 01EV]
lemma oppositeFunctor_square : SSet.opFunctor.{u} ⋙ SSet.opFunctor = 𝟭 SSet.{u} := by
  exact Functor.ext_of_iso SSet.opFunctorCompOpFunctorIso
    opposite_opposite_eq opposite_doubleIso_eqToHom

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
