module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCommonIndex

/-! # 共通面での境界データの一致

概要：左右の零未知境界データを共通面へ制限すると、全ての既知面で一致する。
方針：共通面と後続の面の合成を交換し、小さい二セルの共通面の一致を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：可変部分と A 側の残差成分を左右で同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：左右の境界への面の持ち上げは、その共通面上で一致する。
方針：小さい二セルの pushout の可換性に同じ境界面の包含を合成する。
規約：HTT §1.2.13。使われ方：共通面の既知の境界データの一致。 -/
lemma spanBoundaryLifts_common (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift.{u} n j hj =
      SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift
  rw [← Category.assoc, ← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout n).w]

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左右の零未知データの共通面への制限は、各後続面で一致する。
方針：引き戻しの合成を交換し、元の境界写像を共通の持ち上げで評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：共通データの外延性の既知面の前提。 -/
lemma spanBoundaryCommonData_face {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)).pullback
        j.succ.succAboveOrderEmb.toOrderHom =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)).pullback
        j.succ.succAboveOrderEmb.toOrderHom := by
  have hj : j.succ.succ ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hLeft := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) j.succ.succ hj
  have hRight := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_pullback_face F
    (fun _ _ _ _ _ _ _ _ => 0) j.succ.succ hj
  have hres :
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j.succ.succ hj ≫ F)).toSimplexData.pullback
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n).succAboveOrderEmb.toOrderHom =
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j.succ.succ hj ≫ F)).toSimplexData.pullback
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n).succAboveOrderEmb.toOrderHom := by
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j.succ.succ hj ≫ F))).toSimplexData =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j.succ.succ hj ≫ F))).toSimplexData
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
    rw [← Category.assoc, ← Category.assoc, spanBoundaryLifts_common]
  rw [← hLeft, ← hRight] at hres
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommon_orderHom_comp]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp] using hres

end SerrePositivity.InfinityCategories.Project.DerivedCategories
