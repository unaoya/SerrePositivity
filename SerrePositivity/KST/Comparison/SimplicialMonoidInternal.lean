module

public import SerrePositivity.KST.Comparison.MonoidComponents
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 単体的モノイドと内部モノイドの間の移送

概要：MonCat に値を取る単体的対象と、単体集合のモノイド対象の間の標準的な移送を定義する。
方針：Mathlib の関手圏の内部モノイドと Type の内部モノイドの二つの同値を使う。
規約：KST Lemma 2.13 の bar の入力は従来どおり SimplicialObject MonCat とする。
使われ方：monoidal な Kan 置換を既存の bar の入力に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Monoidal

/--
概要：単体的モノイドを単体集合の内部モノイドへ送る関手。
方針：各次数で MonCat を Type の内部モノイドへ送り、関手圏の内部モノイドにまとめる。
規約：既存の bar の入力を変更せず補助的な内部モノイドの界面を使う。
使われ方：Ex∞ の monoidal 関手を適用する準備。
-/
def simplicialMonoidToInternal : SimplicialObject MonCat.{u} ⥤ Mon SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ MonCat (Mon (Type u))).obj
      monTypeEquivalenceMon.inverse ⋙
    (monFunctorCategoryEquivalence SimplexCategoryᵒᵖ (Type u)).inverse

/--
概要：単体集合の内部モノイドを単体的モノイドへ送る関手。
方針：関手圏の内部モノイドを各次数のモノイドへ分解し、MonCat へ移す。
規約：bar の一対象圏の nerve の構成に使う入力へ戻す。
使われ方：Kan 置換後のモノイドの bar。
-/
def internalMonoidToSimplicial : Mon SSet.{u} ⥤ SimplicialObject MonCat.{u} :=
  (monFunctorCategoryEquivalence SimplexCategoryᵒᵖ (Type u)).functor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (Mon (Type u)) MonCat).obj
      monTypeEquivalenceMon.functor

/--
概要：内部モノイドへ移しても基礎単体集合は既存の monoidSpace に一致する。
方針：二つの標準同値の基礎対象の定義を使う。
規約：単体的対象の面・退化も含めた関手の等式。
使われ方：置換の基礎単体集合の Kan 性と局所化での比較。
-/
theorem simplicialMonoidToInternal_space (M : SimplicialObject MonCat.{u}) :
    (simplicialMonoidToInternal.obj M).X = monoidSpace M := rfl

/--
概要：内部モノイドから戻した単体的モノイドの基礎単体集合は元の基礎対象である。
方針：標準同値の対象と射の定義を使う。
規約：bar の行の積座標と内部モノイドの基礎対象を合わせる。
使われ方：置換後の単体的モノイドの Kan 性。
-/
theorem internalMonoidToSimplicial_space (M : Mon SSet.{u}) :
    monoidSpace (internalMonoidToSimplicial.obj M) = M.X := rfl

end SerrePositivity.KST.Comparison
