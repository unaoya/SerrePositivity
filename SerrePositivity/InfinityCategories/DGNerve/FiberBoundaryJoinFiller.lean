module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryCommonFace

/-! # 左右の単体を貼り合わせた join の充填

概要：共通面で一致する左右の実際の単体を標準 cospan の join 上の一つの写像へ貼る。
方針：二セル表示の押し出しの普遍性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：slice の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：左右の単体を表す写像は押し出しの共通面で一致する。
方針：面の Yoneda 公式で単体の共通面の等式へ戻す。
規約：HTT §1.2.13。使われ方：join の二セルの貼合せの整合条件。 -/
lemma fiberBoundaryCells_compatible {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    SSet.stdSimplex.δ ((Fin.last (n + 2)).castSucc) ≫
        (SSet.yonedaEquiv.symm (fiberBoundaryLeftSimplex g h b hb) :
          (Δ[n + 3] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) =
      SSet.stdSimplex.δ ((Fin.last (n + 2)).castSucc) ≫
        SSet.yonedaEquiv.symm (fiberBoundaryRightSimplex g h b hb) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  exact fiberBoundarySimplex_common g h b hb

/-- 概要：左右の単体を標準 cospan の join 上の一写像に貼り合わせる。
方針：二つの標準セルの押し出しに、共通面で一致する二写像を与える。
規約：HTT §1.2.13。使われ方：実際の slice の充填写像の uncurry。 -/
def fiberBoundaryJoinFiller {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    join (Δ[n + 1] : SSet.{u + 1}) (SSet.horn 2 2) ⟶ dgNerve A (Complex A) :=
  (cospanJoin_isPushout (n + 1)).desc
    (SSet.yonedaEquiv.symm (fiberBoundaryLeftSimplex g h b hb))
    (SSet.yonedaEquiv.symm (fiberBoundaryRightSimplex g h b hb))
    (fiberBoundaryCells_compatible g h b hb)

/-- 概要：貼合せた充填の左セルへの制限は構成した左単体。
方針：押し出しの降下の第一の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の左の既知面との比較。 -/
lemma fiberBoundaryJoinFiller_left {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    cospanJoinLeft (n + 1) ≫ fiberBoundaryJoinFiller g h b hb =
      SSet.yonedaEquiv.symm (fiberBoundaryLeftSimplex g h b hb) :=
  (cospanJoin_isPushout (n + 1)).inl_desc _ _ _

/-- 概要：貼合せた充填の右セルへの制限は構成した右単体。
方針：押し出しの降下の第二の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の右の既知面との比較。 -/
lemma fiberBoundaryJoinFiller_right {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    cospanJoinRight (n + 1) ≫ fiberBoundaryJoinFiller g h b hb =
      SSet.yonedaEquiv.symm (fiberBoundaryRightSimplex g h b hb) :=
  (cospanJoin_isPushout (n + 1)).inr_desc _ _ _

end SerrePositivity.InfinityCategories.DGNerve
