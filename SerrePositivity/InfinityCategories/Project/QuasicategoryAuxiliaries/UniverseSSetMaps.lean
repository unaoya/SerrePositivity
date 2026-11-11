module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.NatIso


/-!
概要：単体集合の宇宙の持ち上げの完全忠実性と直積・標準単体の同型。
方針：型の ULift の完全忠実性を関手圏へ移し、同型は各次数の値で構成する。
規約：標準単体の二段の ULift を明示して交換する。
使われ方：HTT 4.2.4.1 の weighted nerve の切断空間の宇宙の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：単体集合の ULift 関手は完全忠実。
方針：型の ULift 関手の完全忠実性を成分ごとの後合成に移す。
規約：添字圏は同じ単体圏の反対。
使われ方：HTT 4.2.4.1 の切断の族を元の宇宙に一意に戻す。 -/
def uliftSSetFullyFaithful : (SSet.uliftFunctor.{v, u}).FullyFaithful :=
  CategoryTheory.fullyFaithfulULiftFunctor.whiskeringRight SimplexCategoryᵒᵖ

/-- 概要：単体集合の ULift 関手の充満性。
方針：完全忠実性の構成から取り出す。
規約：戻す射は各成分で ULift.down を適用したもの。
使われ方：HTT 4.2.4.1 の切断の族の逆対応。 -/
instance uliftSSetFunctor_full : (SSet.uliftFunctor.{v, u}).Full := uliftSSetFullyFaithful.full

/-- 概要：単体集合の ULift 関手の忠実性。
方針：完全忠実性の構成から取り出す。
規約：射の等式は持ち上げた後で検出できる。
使われ方：HTT 4.2.4.1 の切断の固定条件の降下。 -/
instance uliftSSetFunctor_faithful : (SSet.uliftFunctor.{v, u}).Faithful :=
  uliftSSetFullyFaithful.faithful

/-- 概要：単体集合の直積の ULift は各因子の ULift の直積と同型。
方針：ULift された対と ULift の対を各次数で交換する。
規約：二つの因子の元の宇宙は共通 u。
使われ方：HTT 4.2.4.1 の切断の普遍的な評価の持ち上げ。 -/
def uliftTensorIso (X Y : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj (X ⊗ Y) ≅
      (SSet.uliftFunctor.{v, u}).obj X ⊗ (SSet.uliftFunctor.{v, u}).obj Y :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso {
    toFun a := (ULift.up a.down.1, ULift.up a.down.2)
    invFun a := ULift.up (a.1.down, a.2.down)
    left_inv _ := rfl
    right_inv _ := rfl }) (fun _ ↦ by rfl)

/-- 概要：直積の ULift の同型の逆は第二因子の射と可換。
方針：各次数の対の両成分を計算する。
規約：第一因子は固定。
使われ方：HTT 4.2.4.1 の切断のパラメータの自然性。 -/
lemma uliftTensorIso_inv_whiskerLeft (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B) :
    ((SSet.uliftFunctor.{v, u}).obj K ◁ (SSet.uliftFunctor.{v, u}).map f) ≫
      (uliftTensorIso K B).inv =
    (uliftTensorIso K A).inv ≫ (SSet.uliftFunctor.{v, u}).map (K ◁ f) := rfl

/-- 概要：標準単体の ULift は大きい宇宙の同じ標準単体と同型。
方針：順序写像を包む二段の ULift を一段へまとめる。
規約：頂点番号と単体圏の射は変更しない。
使われ方：HTT 4.2.4.1 の切断空間の各次数の全単射の検証。 -/
def uliftStdSimplexIso (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (Δ[n] : SSet.{u}) ≅ (Δ[n] : SSet.{max u v}) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso {
    toFun a := ULift.up a.down.down
    invFun a := ULift.up (ULift.up a.down)
    left_inv _ := rfl
    right_inv _ := rfl }) (fun _ ↦ by rfl)

/-- 概要：標準単体の同型で移した Yoneda 射の ULift は持ち上げた simplex の Yoneda 射。
方針：各次数で単体圏の射による引き戻しを計算する。
規約：始域は大きい宇宙の標準単体。
使われ方：HTT 4.2.4.1 の切断空間の比較射の成分の同定。 -/
lemma uliftYonedaMap {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) :
    (uliftStdSimplexIso.{u, v} n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm s) =
    SSet.yonedaEquiv.symm (ULift.up s) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
