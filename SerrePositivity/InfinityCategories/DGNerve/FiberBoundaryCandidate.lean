module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundarySolution
public import SerrePositivity.InfinityCategories.DGNerve.ReplacementLocality

/-! # 標準 fiber の境界の明示解を挿入したデータ

概要：解いた先頭成分と D 側成分を左右の零未知データへ挿入する。
方針：共通の型付き解を生の対象へ移し、二つの集合の成分だけ置き換える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：全方程式と貼合せを検証する候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側の対象に移した先頭・D 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque fiberBoundaryLeftNative {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    ({a : GradedHom A ((fiberBoundaryLeftBase g h b).obj 0)
      ((fiberBoundaryLeftBase g h b).obj (cospanApex n)) (fiberBoundaryDegree n + 1) //
      HEq a (fiberBoundaryUnknownA g h b hb)}) ×
    ({d : GradedHom A ((fiberBoundaryLeftBase g h b).obj 0)
      ((fiberBoundaryLeftBase g h b).obj (cospanLastTail n)) (fiberBoundaryDegree n) //
      HEq d (fiberBoundaryUnknownD g h b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := Complex A) (rfl)
      (fiberSliceBoundary_left_apex g h b hb).symm rfl (fiberBoundaryUnknownA g h b hb),
    gradedHomTransportWithHEq (A := A) (D := Complex A) (rfl)
      (fiberSliceBoundary_left_D g h b hb).symm rfl (fiberBoundaryUnknownD g h b hb)⟩

/-- 概要：Left 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と D を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def fiberBoundaryLeftCandidate {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : SimplexData A (Complex A) (n + 3) :=
  ((fiberBoundaryLeftBase g h b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [fiberBoundaryDegree]; push_cast; omega)
    (fiberBoundaryLeftNative g h b hb).1.val).replaceFixed
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (fiberBoundaryDegree n)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
      (cospanPrefix_insert_min _ _)
      (cospanPrefix_insert_max _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
          dsimp only [fiberBoundaryDegree]
          push_cast
          omega)
      (fiberBoundaryLeftNative g h b hb).2.val

/-- 概要：Right 側の対象に移した先頭・D 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque fiberBoundaryRightNative {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    ({a : GradedHom A ((fiberBoundaryRightBase g h b).obj 0)
      ((fiberBoundaryRightBase g h b).obj (cospanApex n)) (fiberBoundaryDegree n + 1) //
      HEq a (fiberBoundaryUnknownA g h b hb)}) ×
    ({d : GradedHom A ((fiberBoundaryRightBase g h b).obj 0)
      ((fiberBoundaryRightBase g h b).obj (cospanLastTail n)) (fiberBoundaryDegree n) //
      HEq d (fiberBoundaryUnknownD g h b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := Complex A) (fiberBoundarySource_right_eq g h b).symm
      (fiberSliceBoundary_right_apex g h b hb).symm rfl (fiberBoundaryUnknownA g h b hb),
    gradedHomTransportWithHEq (A := A) (D := Complex A) (fiberBoundarySource_right_eq g h b).symm
      (fiberSliceBoundary_right_D g h b hb).symm rfl (fiberBoundaryUnknownD g h b hb)⟩

/-- 概要：Right 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と D を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def fiberBoundaryRightCandidate {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : SimplexData A (Complex A) (n + 3) :=
  ((fiberBoundaryRightBase g h b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [fiberBoundaryDegree]; push_cast; omega)
    (fiberBoundaryRightNative g h b hb).1.val).replaceFixed
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (fiberBoundaryDegree n)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
      (cospanPrefix_insert_min _ _)
      (cospanPrefix_insert_max _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
          dsimp only [fiberBoundaryDegree]
          push_cast
          omega)
      (fiberBoundaryRightNative g h b hb).2.val

end SerrePositivity.InfinityCategories.DGNerve
