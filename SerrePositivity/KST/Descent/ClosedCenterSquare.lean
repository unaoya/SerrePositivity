module

public import SerrePositivity.KST.Descent.ReducedClosedSubscheme
public import SerrePositivity.KST.Descent.BlowupGeometry

/-!
# 被約閉中心による実際の Cartesian 正方形

## 概要
有限型スキームの射と被約閉中心から、その引き戻しを有限型スキームの圏内で構成する。
射が固有で中心の補集合上で同型なら、実際の抽象 blowup 正方形を得る。

## 方針
スキームの引き戻しを取り、閉埋め込みの底変換によって左上の有限型性を証明する。
四つの射が同じ基底上の射であることを確認し、Cartesian 性も証明する。

## 規約
中心が被約でもその引き戻しが被約であるとは仮定しない。
proper 性と補集合での実際の同型は、具体的な射の構成側で証明して入力する。

## 使われ方
論文 補題 3.3 の平坦化正方形と定理 3.1 の軌道正方形を、公理 (2) の幾何入力へ移す。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y : FiniteTypeSchemes S}

/-- 概要：有限型スキームの射に沿う被約閉中心の引き戻し（論文 §3）。
方針：実際のスキームの引き戻しの第一射影が閉埋め込みであることを使う。
規約：引き戻しの被約性は要求せず、有限型性だけを保持する。
使われ方：抽象 blowup 正方形の左上の例外部分。 -/
noncomputable def closedCenterPullback (f : Y ⟶ X) (Z : Closeds X.obj.left) :
    FiniteTypeSchemes S := by
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (pullback.fst f.hom.left (reducedClosedInclusion Z) ≫ Y.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：中心の引き戻しから変形先への第一射影（論文 §3）。
方針：スキームの引き戻しの第一射影を基底上の射として包む。
規約：有限型スキームの圏の射。
使われ方：抽象 blowup 正方形の上辺。 -/
noncomputable def closedCenterPullbackFirst (f : Y ⟶ X) (Z : Closeds X.obj.left) :
    closedCenterPullback f Z ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.hom.left (reducedClosedInclusion Z)))

/-- 概要：中心の引き戻しから被約閉中心への第二射影（論文 §3）。
方針：引き戻しの可換式と f の基底との両立を使い、基底上の射であることを確認する。
規約：中心の構造射との可換式を保持する。
使われ方：抽象 blowup 正方形の左辺。 -/
noncomputable def closedCenterPullbackSecond (f : Y ⟶ X) (Z : Closeds X.obj.left) :
    closedCenterPullback f Z ⟶ reducedClosedAsFiniteType X Z :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f.hom.left (reducedClosedInclusion Z)) (by
    change pullback.snd f.hom.left (reducedClosedInclusion Z) ≫
      (reducedClosedInclusion Z ≫ X.obj.hom) =
      pullback.fst f.hom.left (reducedClosedInclusion Z) ≫ Y.obj.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, f.hom.w]))

/-- 概要：被約閉中心を引き戻した有限型スキームの可換正方形（論文 §3）。
方針：二つの射影と元の射・中心の包含を組み合わせる。
規約：四頂点とも基底 S 上有限型。
使われ方：前層 L の実際の制限写像の正方形。 -/
noncomputable def closedCenterSquare (f : Y ⟶ X) (Z : Closeds X.obj.left) :
    Square (FiniteTypeSchemes S) where
  f₁₂ := closedCenterPullbackFirst f Z
  f₁₃ := closedCenterPullbackSecond f Z
  f₂₄ := f
  f₃₄ := reducedClosedAsFiniteTypeInclusion X Z
  fac := by
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact pullback.condition

/-- 概要：中心の引き戻し正方形はスキームの圏で Cartesian（論文 §3）。
方針：構成に用いた実際のスキームの引き戻しの普遍性を使う。
規約：有限型対象に限定した普遍性ではない。
使われ方：抽象 blowup の Cartesian 条件を満たす。 -/
theorem closedCenterSquare_cartesian (f : Y ⟶ X) (Z : Closeds X.obj.left) :
    IsPullback (closedCenterSquare f Z).f₁₂.hom.left (closedCenterSquare f Z).f₁₃.hom.left
      (closedCenterSquare f Z).f₂₄.hom.left (closedCenterSquare f Z).f₃₄.hom.left :=
  IsPullback.of_hasPullback f.hom.left (reducedClosedInclusion Z)

/-- 概要：被約閉中心の補開集合（論文 §3）。
方針：閉集合の補集合に開スキームの構造を入れる。
規約：中心の nilpotent な構造によらず台で補集合を取る。
使われ方：固有射が同型になる範囲。 -/
def closedCenterComplement (Z : Closeds X.obj.left) : X.obj.left.Opens :=
  ⟨(Z : Set X.obj.left)ᶜ, Z.isClosed.isOpen_compl⟩

/-- 概要：中心の外で同型な固有射から実際の抽象 blowup 正方形を構成（論文 §3）。
方針：閉中心の引き戻しで四頂点と Cartesian 性を構成し、固有性と外での同型を合わせる。
規約：この幾何構成自体は前層 L の降下や主定理を仮定しない。
使われ方：平坦化・軌道正方形を公理 (2) の入力にする。 -/
noncomputable def abstractBlowupOfReducedCenter (f : Y ⟶ X) (Z : Closeds X.obj.left)
    [IsProper f.hom.left] (outside_iso : IsIso (f.hom.left ∣_ closedCenterComplement Z)) :
    AbstractBlowupSquare S where
  square := closedCenterSquare f Z
  cartesian := closedCenterSquare_cartesian f Z
  proper := show IsProper f.hom.left from inferInstance
  closed := by
    change IsClosedImmersion (reducedClosedInclusion Z)
    infer_instance
  complement := closedCenterComplement Z
  complement_eq := by
    change (Z : Set X.obj.left)ᶜ = (Set.range (reducedClosedInclusion Z))ᶜ
    rw [range_reducedClosedInclusion]
  iso_on_complement := outside_iso

end SerrePositivity.KST.Descent
