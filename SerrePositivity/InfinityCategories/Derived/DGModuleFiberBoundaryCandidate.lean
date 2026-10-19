module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundarySolution
public import SerrePositivity.InfinityCategories.DGNerve.ReplacementLocality

/-! # 標準 fiber の境界の明示解を挿入したデータ

概要：解いた先頭成分と N 側成分を左右の零未知データへ挿入する。
方針：共通の型付き解を生の対象へ移し、二つの集合の成分だけ置き換える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：全方程式と貼合せを検証する候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：Left 側の対象に移した先頭・N 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque dgModuleFiberBoundaryLeftNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    ({a : GradedHom A ((dgModuleFiberBoundaryLeftBase A D f b).obj 0)
      ((dgModuleFiberBoundaryLeftBase A D f b).obj (cospanApex n)) (dgModuleFiberBoundaryDegree n
        + 1) //
      HEq a (dgModuleFiberBoundaryUnknownA A D f b hb)}) ×
    ({d : GradedHom A ((dgModuleFiberBoundaryLeftBase A D f b).obj 0)
      ((dgModuleFiberBoundaryLeftBase A D f b).obj (cospanLastTail n))
        (dgModuleFiberBoundaryDegree n) //
      HEq d (dgModuleFiberBoundaryUnknownN A D f b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := RightModule A D) (rfl)
      (dgModuleFiberBoundary_left_apex A D f b hb).symm rfl (dgModuleFiberBoundaryUnknownA A D f b
        hb),
    gradedHomTransportWithHEq (A := A) (D := RightModule A D) (rfl)
      (dgModuleFiberBoundary_left_N A D f b hb).symm rfl (dgModuleFiberBoundaryUnknownN A D f b hb)⟩

/-- 概要：Left 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と N を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def dgModuleFiberBoundaryLeftCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : SimplexData A (RightModule A D) (n + 3) :=
  ((dgModuleFiberBoundaryLeftBase A D f b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryLeftNative A D f b hb).1.val).replaceFixed
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (dgModuleFiberBoundaryDegree n)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
      (cospanPrefix_insert_min _ _)
      (cospanPrefix_insert_max _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
          dsimp only [dgModuleFiberBoundaryDegree]
          push_cast
          omega)
      (dgModuleFiberBoundaryLeftNative A D f b hb).2.val

/-- 概要：Right 側の対象に移した先頭・N 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque dgModuleFiberBoundaryRightNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    ({a : GradedHom A ((dgModuleFiberBoundaryRightBase A D f b).obj 0)
      ((dgModuleFiberBoundaryRightBase A D f b).obj (cospanApex n)) (dgModuleFiberBoundaryDegree n
        + 1) //
      HEq a (dgModuleFiberBoundaryUnknownA A D f b hb)}) ×
    ({d : GradedHom A ((dgModuleFiberBoundaryRightBase A D f b).obj 0)
      ((dgModuleFiberBoundaryRightBase A D f b).obj (cospanLastTail n))
        (dgModuleFiberBoundaryDegree n) //
      HEq d (dgModuleFiberBoundaryUnknownN A D f b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := RightModule A D) (dgModuleFiberBoundarySource_right_eq
    A D f b).symm
      (dgModuleFiberBoundary_right_apex A D f b hb).symm rfl (dgModuleFiberBoundaryUnknownA A D f
        b hb),
    gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (dgModuleFiberBoundarySource_right_eq A D f b).symm
      (dgModuleFiberBoundary_right_N A D f b hb).symm rfl (dgModuleFiberBoundaryUnknownN A D f b
        hb)⟩

/-- 概要：Right 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と N を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def dgModuleFiberBoundaryRightCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : SimplexData A (RightModule A D) (n + 3) :=
  ((dgModuleFiberBoundaryRightBase A D f b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryRightNative A D f b hb).1.val).replaceFixed
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (dgModuleFiberBoundaryDegree n)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
      (cospanPrefix_insert_min _ _)
      (cospanPrefix_insert_max _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
      (by rw [card_cospanPrefix_insert _
            ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
          dsimp only [dgModuleFiberBoundaryDegree]
          push_cast
          omega)
      (dgModuleFiberBoundaryRightNative A D f b hb).2.val

end SerrePositivity.InfinityCategories
