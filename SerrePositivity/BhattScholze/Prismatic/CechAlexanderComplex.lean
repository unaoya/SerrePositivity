module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexanderAssembly
public import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Čech–Alexander 対象の交代余面複体

## 概要
HasEnvelopes からの余単体的対象とその mod d の剰余を、通常の A 加群の複体として読む。

## 方針
基底の下の環から加群を取り、Mathlib の交代余面複体を適用する。

## 規約
BS 著者版 Construction 4.18。非正規化複体で、Tot や導来極限との同一視は G10 の後。

## 使われ方
後の Hodge–Tate 比較と底変換の計算模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory AlgebraicTopology
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

/-- 概要：site の各剰余環を基底の剰余環の下の代数として読む。
方針：prism 射の quotientMap と基底上の可換性を使う。
規約：BS 著者版 Definition 4.1、Construction 4.18。
使われ方：mod d の余単体的加群と交代余面複体。 -/
def prismSiteReducedAlgebras : PrismOver P R κ ⥤ Under (CommRingCat.of (A ⧸ P.ideal)) where
  obj X := Under.mk (CommRingCat.ofHom X.toHom.quotientMap)
  map {X Y} f := Under.homMk (CommRingCat.ofHom f.toHom.quotientMap) (by
    apply CommRingCat.hom_ext
    change f.toHom.quotientMap.comp X.toHom.quotientMap = Y.toHom.quotientMap
    rw [← OrientedPrism.Hom.quotientMap_comp, f.comm_base])
  map_id X := Under.UnderMorphism.ext (by
    apply CommRingCat.hom_ext
    exact OrientedPrism.Hom.quotientMap_id X.Q)
  map_comp f g := Under.UnderMorphism.ext (by
    apply CommRingCat.hom_ext
    exact OrientedPrism.Hom.quotientMap_comp g.toHom f.toHom)

variable (h : HasEnvelopes P R) (hκ : cutoff A R ≤ κ)

/-- 概要：Čech–Alexander の交代余面複体 C^•。
方針：各環の A 加群を取り、既存の alternatingCofaceMapComplex を適用する。
規約：BS 著者版 Construction 4.18。使われ方：通常の複体による計算の入力。 -/
def cechAlexanderComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj
    (cechAlexander P R h κ hκ ⋙ prismSiteAlgebras P R κ ⋙ Cech.underToModule (CommRingCat.of A))

/-- 概要：mod d の Čech–Alexander の交代余面複体 C^•/d。
方針：各 prism の剰余を A/d 加群として読み、A へ係数を制限する。
規約：BS 著者版 Construction 4.18。使われ方：Hodge–Tate 比較の古典的な計算模型。 -/
def cechAlexanderReducedComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj
    (cechAlexander P R h κ hκ ⋙ prismSiteReducedAlgebras P R κ ⋙
      Cech.underToModule (CommRingCat.of (A ⧸ P.ideal)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk P.ideal))

end SerrePositivity.BhattScholze.Prismatic
