module

public import SerrePositivity.KST.Descent.ClosedPullbackAction

/-!
# 四頂点と四辺を保つ群作用

## 概要
可換正方形の各頂点の作用と、四辺の同変性をまとめる。
閉中心の実際の引き戻し正方形について、このデータを構成する。

## 方針
左上の作用を引き戻し上で構成し、両射影の同変性を用いる。

## 規約
前層の長完全列の境界の同変性は、この幾何データとは別に自然性から供給する。

## 使われ方
論文 定理 3.1 の G 同変な軌道正方形を、前層 L の指定制限へ接続する。
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：四頂点と指定四辺の同変性を持つ可換正方形（論文 定理 3.1）。
方針：各自己同型群への準同型と辺の指定可換式を保持する。
規約：射の同変性から境界の同変性を自動には推論しない。
使われ方：軌道正方形を同変な前層の列へ適用する。 -/
structure SquareAction {C : Type u} [Category.{v} C] (s : Square C)
    (G : Type*) [Group G] where
  /-- 概要：左上の作用（論文 §3）。方針：自己同型群への準同型。
  規約：例外部分の作用。使われ方：差の終域。 -/
  on1 : G →* Aut s.X₁
  /-- 概要：右上の作用（論文 §3）。方針：自己同型群への準同型。
  規約：固有な変形の作用。使われ方：置換表現。 -/
  on2 : G →* Aut s.X₂
  /-- 概要：左下の作用（論文 §3）。方針：自己同型群への準同型。
  規約：閉中心の作用。使われ方：次元帰納。 -/
  on3 : G →* Aut s.X₃
  /-- 概要：右下の作用（論文 §3）。方針：自己同型群への準同型。
  規約：元の対象の作用。使われ方：降下比較。 -/
  on4 : G →* Aut s.X₄
  /-- 概要：上辺の同変性（論文 §3）。方針：指定可換式。
  規約：正方形の射そのもの。使われ方：前層の制限。 -/
  equivariant12 : ∀ g, (on1 g).asIso.hom ≫ s.f₁₂ = s.f₁₂ ≫ (on2 g).asIso.hom
  /-- 概要：左辺の同変性（論文 §3）。方針：指定可換式。
  規約：正方形の射そのもの。使われ方：前層の制限。 -/
  equivariant13 : ∀ g, (on1 g).asIso.hom ≫ s.f₁₃ = s.f₁₃ ≫ (on3 g).asIso.hom
  /-- 概要：右辺の同変性（論文 §3）。方針：指定可換式。
  規約：固有射そのもの。使われ方：降下比較の自然性。 -/
  equivariant24 : ∀ g, (on2 g).asIso.hom ≫ s.f₂₄ = s.f₂₄ ≫ (on4 g).asIso.hom
  /-- 概要：下辺の同変性（論文 §3）。方針：指定可換式。
  規約：閉埋め込みそのもの。使われ方：中心の比較。 -/
  equivariant34 : ∀ g, (on3 g).asIso.hom ≫ s.f₃₄ = s.f₃₄ ≫ (on4 g).asIso.hom

/-- 概要：同変な閉中心の実際の引き戻し正方形の G 作用（論文 定理 3.1）。
方針：左上の作用を構成済みの引き戻し作用で供給する。
規約：被約性や前層の降下を仮定しない。
使われ方：軌道正方形の四頂点と四辺の同変性。 -/
noncomputable def closedImmersionSquareAction {S : Scheme.{u}}
    {X Y Z : FiniteTypeSchemes S} {G : Type*} [Group G]
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (actionY : G →* Aut Y) (actionZ : G →* Aut Z) (actionX : G →* Aut X)
    (equivariant_f : ∀ g, (actionY g).asIso.hom ≫ f = f ≫ (actionX g).asIso.hom)
    (equivariant_i : ∀ g, (actionZ g).asIso.hom ≫ i = i ≫ (actionX g).asIso.hom) :
    SquareAction (closedImmersionSquare f i) G where
  on1 := closedPullbackAction f i actionY actionZ actionX equivariant_f equivariant_i
  on2 := actionY
  on3 := actionZ
  on4 := actionX
  equivariant12 := closedPullbackAction_fst f i actionY actionZ actionX equivariant_f equivariant_i
  equivariant13 := closedPullbackAction_snd f i actionY actionZ actionX equivariant_f equivariant_i
  equivariant24 := equivariant_f
  equivariant34 := equivariant_i

end SerrePositivity.KST.Descent
