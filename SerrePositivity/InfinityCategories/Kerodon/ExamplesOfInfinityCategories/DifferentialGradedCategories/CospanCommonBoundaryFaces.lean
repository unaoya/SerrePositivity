module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanCommonIndex

/-! # 共通面での境界データの一致

概要：左右の零未知境界データを共通面へ制限すると、全ての既知面で一致する。
方針：共通面と先頭の面の合成を交換し、小さい二セルの共通面の一致を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：先頭と D の残差成分を左右で同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：左右の境界への面の持ち上げは、その共通面上で一致する。
方針：小さい二セルの pushout の可換性に同じ境界面の包含を合成する。
規約：HTT §1.2.13。使われ方：共通面の既知の境界データの一致。 -/
lemma cospanBoundaryLifts_common (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftLift.{u} n j hj =
      SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightLift n j hj := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftLift _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightLift
  rw [← Category.assoc, ← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout n).w]

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左右の零未知データの共通面への制限は、各先頭面で一致する。
方針：引き戻しの合成を交換し、元の境界写像を共通の持ち上げで評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：共通データの外延性の既知面の前提。 -/
lemma cospanBoundaryCommonData_face {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n)).pullback
        j.castSucc.succAboveOrderEmb.toOrderHom =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n)).pullback
        j.castSucc.succAboveOrderEmb.toOrderHom := by
  have hj : j.castAdd 2 ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hLeft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) (j.castAdd 2) hj
  have hRight := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) (j.castAdd 2) hj
  have hres :
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftLift n (j.castAdd 2) hj ≫ F)).toSimplexData.pullback
          ((Fin.last (n + 1)).castSucc).succAboveOrderEmb.toOrderHom =
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightLift n (j.castAdd 2) hj ≫ F)).toSimplexData.pullback
          ((Fin.last (n + 1)).castSucc).succAboveOrderEmb.toOrderHom := by
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ ((Fin.last (n + 1)).castSucc)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftLift n (j.castAdd 2) hj ≫ F))).toSimplexData =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ ((Fin.last (n + 1)).castSucc)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightLift n (j.castAdd 2) hj ≫ F))).toSimplexData
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
    rw [← Category.assoc, ← Category.assoc, cospanBoundaryLifts_common]
  rw [← hLeft, ← hRight] at hres
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommon_orderHom_comp]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp] using hres

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
