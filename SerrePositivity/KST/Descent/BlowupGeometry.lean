module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Descent.Axioms
public import Mathlib.CategoryTheory.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# 論文 §3 の抽象 blowup 正方形の幾何学的な入力

## 概要
有限型スキーム上の Cartesian 正方形で、右辺が固有、下辺が閉埋め込み、
閉中心の補開集合上で右辺が同型になるものを保持する。

## 方針
Mathlib の可換正方形を使い、実際のスキームの引き戻し性と射の性質を別に記録する。

## 規約
KST 定理 A の pro 降下や L の降下はこの幾何データに含めない。
Milnor 正方形の条件や単なる点集合の Cartesian 性に弱めない。

## 使われ方
論文 補題 3.3 の閉和・平坦化 blowup、定理 3.1 の G 同変な軌道正方形、公理 (2)。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SerrePositivity.KST.Descent

/-- 概要：有限型の条件と基底の構造射を忘れてスキームを得る（論文 §3）。
方針：充満部分圏の包含と `Over.forget` を合成する。
規約：射は実際のスキームの射に送る。
使われ方：有限型スキーム上の正方形に固有性・閉埋め込み・引き戻し性を課す。 -/
def finiteTypeSchemesForget (S : Scheme.{u}) : FiniteTypeSchemes S ⥤ Scheme.{u} :=
  ObjectProperty.ι (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙
    Over.forget S

/-- 概要：論文 §3 に現れる抽象 blowup 正方形（補題 3.3・定理 3.1）。
方針：有限型スキームの可換正方形に、実際のスキームの幾何学的条件を付ける。
規約：左上が例外部分、右上が固有な変形、左下が閉中心、右下が元のスキーム。
使われ方：公理 (2) の適用対象。L の実降下の証明や仮定は別に保持する。 -/
structure AbstractBlowupSquare (S : Scheme.{u}) where
  /-- 概要：有限型 S スキームの可換正方形（論文 §3）。
  方針：Mathlib の `Square` とその可換式を保持する。
  規約：点集合だけの図式ではない。
  使われ方：前層 L の反変な制限写像を指定する。 -/
  square : Square (FiniteTypeSchemes S)
  /-- 概要：スキームの圏での Cartesian 性（論文 補題 3.3・定理 3.1）。
  方針：有限型の条件を忘れた後の実際の射に `IsPullback` を要求する。
  規約：有限型対象だけに限定した普遍性ではない。
  使われ方：閉中心の引き戻しを例外部分として特定する。 -/
  cartesian : IsPullback square.f₁₂.hom.left square.f₁₃.hom.left
    square.f₂₄.hom.left square.f₃₄.hom.left
  /-- 概要：右辺の固有性（論文 補題 3.3・定理 3.1）。
  方針：実際のスキームの射に Mathlib の固有性を課す。
  規約：blowup そのものであることは要求しない。
  使われ方：抽象 blowup 降下の適用。 -/
  proper : IsProper square.f₂₄.hom.left
  /-- 概要：下辺は閉中心の埋め込み（論文 補題 3.3・定理 3.1）。
  方針：スキームの閉埋め込みを要求する。
  規約：閉集合の包含だけではない。
  使われ方：中心の補集合を開スキームとして取る。 -/
  closed : IsClosedImmersion square.f₃₄.hom.left
  /-- 概要：閉中心の補開集合（論文 §3）。
  方針：実際の開集合と、その中心の像との関係を保持する。
  規約：任意の稠密開集合に置き換えない。
  使われ方：右辺の制限が同型になる場所。 -/
  complement : square.X₄.obj.left.Opens
  /-- 概要：補開集合は閉中心の像の補集合（論文 §3）。
  方針：基礎位相空間の集合として等しいことを記録する。
  規約：中心が空や全体の場合も許す。
  使われ方：軌道の一致場所や平坦化の中心と同型範囲を結び付ける。 -/
  complement_eq : (complement : Set square.X₄.obj.left) =
    (Set.range square.f₃₄.hom.left)ᶜ
  /-- 概要：右辺の補開集合への制限は同型（論文 補題 3.3・定理 3.1）。
  方針：実際のスキームの制限射に同型性を要求する。
  規約：点集合の全単射性だけに弱めない。
  使われ方：公理 (2) の補集合での同型条件。 -/
  iso_on_complement : IsIso (square.f₂₄.hom.left ∣_ complement)

end SerrePositivity.KST.Descent

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (1.1)" (partial := special) "仮定：固定基底 S 上の有限型スキームで、固有射・閉埋め込み・補開上の同型（Lean が強い：有限型の表示を指定）。結論：引き戻しで与えた例外因子を持つ抽象ブローアップ正方形（原典と一致）。"] _root_.SerrePositivity.KST.Descent.AbstractBlowupSquare
attribute [cite KST "Eq (1.9)" (partial := component) "仮定：固定基底上の有限型スキーム、またはアフィン上の指定された通常ブローアップ（Lean が強い）。結論：抽象正方形の条件と通常例外因子の閉性。アフィン正則列中心の四角形として束ねた宣言は確認できない（Lean が弱い）。"] _root_.SerrePositivity.KST.Descent.AbstractBlowupSquare
attribute [cite LT "Eq (21)" (partial := special) "仮定：固定基底 S 上の有限型スキームと固有射・閉中心・補開上の同型（Lean が強い）。結論：実引き戻し正方形を与える。一般の qcqs 上で有限表示の閉中心を指定する原典とは範囲が異なる（Lean が弱い）。"] _root_.SerrePositivity.KST.Descent.AbstractBlowupSquare
