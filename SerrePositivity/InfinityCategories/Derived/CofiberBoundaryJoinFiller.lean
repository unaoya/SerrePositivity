module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundarySimplices

/-! # 左右の単体を貼り合わせた join の充填

概要：共通面で一致する左右の実際の単体を標準 span の join 上の一つの写像へ貼る。
方針：二セル表示の押し出しの普遍性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：coslice の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial

variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：左右の単体を表す写像は押し出しの共通面で一致する。
方針：面の Yoneda 公式で単体の共通面の等式へ戻す。
規約：HTT §1.2.13。使われ方：join の二セルの貼合せの整合条件。 -/
lemma cofiberBoundaryCells_compatible {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    SSet.stdSimplex.δ (spanJoinCommonFace (n + 1)) ≫
        (SSet.yonedaEquiv.symm (cofiberBoundaryLeftSimplex f g b hb) :
          (Δ[n + 3] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (spanJoinCommonFace (n + 1)) ≫
        SSet.yonedaEquiv.symm (cofiberBoundaryRightSimplex f g b hb) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  exact cofiberBoundarySimplex_common f g b hb

/-- 概要：左右の単体を標準 span の join 上の一写像に貼り合わせる。
方針：二つの標準セルの押し出しに、共通面で一致する二写像を与える。
規約：HTT §1.2.13。使われ方：実際の slice の充填写像の uncurry。 -/
def cofiberBoundaryJoinFiller {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    join (SSet.horn 2 0 : SSet.{u + 1}) Δ[n + 1] ⟶ dgNerve S (Complex S) :=
  (spanJoin_isPushout (n + 1)).desc
    (SSet.yonedaEquiv.symm (cofiberBoundaryLeftSimplex f g b hb))
    (SSet.yonedaEquiv.symm (cofiberBoundaryRightSimplex f g b hb))
    (cofiberBoundaryCells_compatible f g b hb)

/-- 概要：貼合せた充填の左セルへの制限は構成した左単体。
方針：押し出しの降下の第一の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の左の既知面との比較。 -/
lemma cofiberBoundaryJoinFiller_left {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    spanJoinLeft (n + 1) ≫ cofiberBoundaryJoinFiller f g b hb =
      SSet.yonedaEquiv.symm (cofiberBoundaryLeftSimplex f g b hb) :=
  (spanJoin_isPushout (n + 1)).inl_desc _ _ _

/-- 概要：貼合せた充填の右セルへの制限は構成した右単体。
方針：押し出しの降下の第二の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の右の既知面との比較。 -/
lemma cofiberBoundaryJoinFiller_right {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    spanJoinRight (n + 1) ≫ cofiberBoundaryJoinFiller f g b hb =
      SSet.yonedaEquiv.symm (cofiberBoundaryRightSimplex f g b hb) :=
  (spanJoin_isPushout (n + 1)).inr_desc _ _ _

end SerrePositivity.InfinityCategories
