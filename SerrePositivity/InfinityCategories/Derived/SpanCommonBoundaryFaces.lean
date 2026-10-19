module
public import SerrePositivity.InfinityCategories.Derived.SpanCommonIndex

/-! # 共通面での境界データの一致

概要：左右の零未知境界データを共通面へ制限すると、全ての既知面で一致する。
方針：共通面と後続の面の合成を交換し、小さい二セルの共通面の一致を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：可変部分と A 側の残差成分を左右で同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

/-- 概要：左右の境界への面の持ち上げは、その共通面上で一致する。
方針：小さい二セルの pushout の可換性に同じ境界面の包含を合成する。
規約：HTT §1.2.13。使われ方：共通面の既知の境界データの一致。 -/
lemma spanBoundaryLifts_common (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    SSet.stdSimplex.δ (spanJoinCommonFace n) ≫ spanBoundaryLeftLift.{u} n j hj =
      SSet.stdSimplex.δ (spanJoinCommonFace n) ≫ spanBoundaryRightLift n j hj := by
  unfold spanBoundaryLeftLift spanBoundaryRightLift
  rw [← Category.assoc, ← Category.assoc, (spanJoin_isPushout n).w]

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左右の零未知データの共通面への制限は、各後続面で一致する。
方針：引き戻しの合成を交換し、元の境界写像を共通の持ち上げで評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：共通データの外延性の既知面の前提。 -/
lemma spanBoundaryCommonData_face {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (j : Fin (n + 2)) :
    ((spanBoundaryLeftZeroData F).pullback (spanCommonOrderHom n)).pullback
        j.succ.succAboveOrderEmb.toOrderHom =
      ((spanBoundaryRightZeroData F).pullback (spanCommonOrderHom n)).pullback
        j.succ.succAboveOrderEmb.toOrderHom := by
  have hj : j.succ.succ ∈ spanSuffixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hLeft := spanBoundaryLeftData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) j.succ.succ hj
  have hRight := spanBoundaryRightData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) j.succ.succ hj
  have hres :
      (SSet.yonedaEquiv (spanBoundaryLeftLift n j.succ.succ hj ≫ F)).toSimplexData.pullback
          (spanJoinCommonFace n).succAboveOrderEmb.toOrderHom =
        (SSet.yonedaEquiv (spanBoundaryRightLift n j.succ.succ hj ≫ F)).toSimplexData.pullback
          (spanJoinCommonFace n).succAboveOrderEmb.toOrderHom := by
    change ((dgNerve A D).δ (spanJoinCommonFace n)
        (SSet.yonedaEquiv (spanBoundaryLeftLift n j.succ.succ hj ≫ F))).toSimplexData =
      ((dgNerve A D).δ (spanJoinCommonFace n)
        (SSet.yonedaEquiv (spanBoundaryRightLift n j.succ.succ hj ≫ F))).toSimplexData
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
    rw [← Category.assoc, ← Category.assoc, spanBoundaryLifts_common]
  rw [← hLeft, ← hRight] at hres
  rw [SimplexData.pullback_comp, SimplexData.pullback_comp, spanCommon_orderHom_comp]
  simpa only [spanBoundaryLeftZeroData, spanBoundaryRightZeroData,
    SimplexData.pullback_comp] using hres

end SerrePositivity.InfinityCategories
