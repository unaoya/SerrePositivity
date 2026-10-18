module

public import SerrePositivity.KST.Descent.BlowupGeometry
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# 任意の閉中心の実際の抽象 blowup 正方形

## 概要
有限型の圏内の閉埋め込みを中心とし、固有射との実際の引き戻し正方形を構成する。

## 方針
スキームの引き戻しの第一射影の閉埋め込み性で有限型性を証明する。
中心の外での指定射の同型性を、抽象 blowup の幾何データへ移す。

## 規約
中心の被約性は要求しない。基底上の閉中心を引き戻して得る非被約な中心も保持する。
前層 L の降下そのものはこの幾何構成の仮定に含めない。

## 使われ方
論文 補題 3.3・定理 3.1 の中心の引き戻しを含む抽象 blowup 正方形。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y Z : FiniteTypeSchemes S}

/-- 概要：任意の閉中心と射の引き戻しを有限型の圏内に構成（論文 §3）。
方針：閉埋め込みの底変換と射の合成の有限型性を使う。
規約：中心にも引き戻しにも被約性を要求しない。
使われ方：抽象 blowup の例外部分。 -/
noncomputable def closedImmersionPullback (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] : FiniteTypeSchemes S := by
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (pullback.fst f.hom.left i.hom.left ≫ Y.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：任意の閉中心による有限型の圏内の可換正方形（論文 §3）。
方針：実際のスキームの引き戻しの両射影を同じ基底上の射にする。
規約：左上のスキーム構造は引き戻しそのもの。
使われ方：前層 L を適用する四つの指定射。 -/
noncomputable def closedImmersionSquare (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] : Square (FiniteTypeSchemes S) where
  f₁₂ := ObjectProperty.homMk (Over.homMk (pullback.fst f.hom.left i.hom.left))
  f₁₃ := ObjectProperty.homMk (Over.homMk (pullback.snd f.hom.left i.hom.left) (by
    change pullback.snd f.hom.left i.hom.left ≫ Z.obj.hom =
      pullback.fst f.hom.left i.hom.left ≫ Y.obj.hom
    rw [← i.hom.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.hom.w]))
  f₂₄ := f
  f₃₄ := i
  fac := by
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact pullback.condition
  X₁ := closedImmersionPullback f i

/-- 概要：構成した任意の閉中心の正方形はスキームの圏で Cartesian（論文 §3）。
方針：構成に用いた引き戻しの普遍性を適用する。
規約：有限型の圏内だけに限定した普遍性ではない。
使われ方：抽象 blowup の Cartesian 条件。 -/
theorem closedImmersionSquare_cartesian (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] :
    IsPullback (closedImmersionSquare f i).f₁₂.hom.left
      (closedImmersionSquare f i).f₁₃.hom.left f.hom.left i.hom.left :=
  IsPullback.of_hasPullback _ _

/-- 概要：閉中心の正方形の第一射影は閉埋め込み（論文 補題 3.3）。
方針：元の閉埋め込みの底変換として判定する。
規約：被約性は要求しない。
使われ方：閉被覆を始域へ引き戻した二つの閉部分。 -/
instance closedImmersionSquare_first_isClosedImmersion (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] : IsClosedImmersion (closedImmersionSquare f i).f₁₂.hom.left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst f.hom.left i.hom.left))

/-- 概要：中心の外で同型な固有射を任意の閉中心の抽象 blowup にする（論文 §3）。
方針：実際の引き戻し正方形と、中心・補集合・指定制限の性質を束ねる。
規約：中心が被約であるという追加条件を要求しない。
使われ方：軌道正方形の、基底の閉中心を引き戻した中心への降下。 -/
noncomputable def abstractBlowupOfClosedImmersion (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] [IsProper f.hom.left] (U : X.obj.left.Opens)
    (complement_eq : (U : Set X.obj.left) = (Set.range i.hom.left)ᶜ)
    (outside_iso : IsIso (f.hom.left ∣_ U)) : AbstractBlowupSquare S where
  square := closedImmersionSquare f i
  cartesian := closedImmersionSquare_cartesian f i
  proper := show IsProper f.hom.left from inferInstance
  closed := show IsClosedImmersion i.hom.left from inferInstance
  complement := U
  complement_eq := complement_eq
  iso_on_complement := outside_iso

end SerrePositivity.KST.Descent
