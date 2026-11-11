module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaTargetBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseDualityLeftEndpoint

/-!
概要：反転した底の表現可能 coslice から、終点固定の twisted arrow への底上の比較。
方針：twisted arrow の双対で両端を交換し、標準二重反転で元の係数へ戻す。
規約：同じ終点固定の射影の pullback へ厳密に持ち上げ、同値性は別に証明する。
使われ方：Yoneda 写像の各対象の表現可能 right fibration との比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 反転した底の twisted arrow を、両端を交換して元の底へ戻す。 -/
def twistedArrowOppositeSwap (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality C.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (SSet.opFunctorCompOpFunctorIso.app C).hom

/-- 両端の交換と二重反転による表示変更は厳密な同型。 -/
instance twistedArrowOppositeSwap_isIso (C : SSet.{u}) : IsIso (twistedArrowOppositeSwap C) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (SSet.opFunctorCompOpFunctorIso.app C).hom) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map
      (SSet.opFunctorCompOpFunctorIso.app C).hom))
  unfold twistedArrowOppositeSwap
  infer_instance

/-- 交換後の左端は、反転した底の元の右端。 -/
lemma twistedArrowOppositeSwap_left (C : SSet.{u}) :
    twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C.op := by
  rw [twistedArrowOppositeSwap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality_left, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.opFunctorCompOpFunctorIso_coherence, Iso.inv_hom_id, Category.comp_id]

/-- 交換後の右端は、反転した底の元の左端を二重反転で戻したもの。 -/
lemma twistedArrowOppositeSwap_right (C : SSet.{u}) :
    twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C.op ≫ (SSet.opFunctorCompOpFunctorIso.app C).hom := by
  rw [twistedArrowOppositeSwap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality_right]

/-- 反転した底の coslice の錐を、元の底の終点固定の twisted arrow へ写す。 -/
def cosliceOppositeTwistedArrowMap {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C.op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap p ≫ twistedArrowOppositeSwap C

/-- 同じ比較の左端は、元の coslice の射影を厳密に保つ。 -/
lemma cosliceOppositeTwistedArrowMap_left {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C.op) :
    cosliceOppositeTwistedArrowMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  rw [cosliceOppositeTwistedArrowMap, Category.assoc, twistedArrowOppositeSwap_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap_right]

/-- 同じ比較の右端は、元の対象の定値写像。 -/
lemma cosliceOppositeTwistedArrowMap_right {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C.op) :
    cosliceOppositeTwistedArrowMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C =
      SSet.const (SSet.opObjEquiv (SSet.yonedaEquiv p)) := by
  rw [cosliceOppositeTwistedArrowMap, Category.assoc, twistedArrowOppositeSwap_right,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap_left, SSet.const_comp]
  rfl

/-- 元の頂点 c で固定した比較は、元の底への射影と厳密に可換。 -/
lemma cosliceOppositeTwistedArrowMap_over {C : SSet.{u}} (c : C _⦋0⦌) :
    cosliceOppositeTwistedArrowMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion c := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst, cosliceOppositeTwistedArrowMap_left,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion, lift_fst, Category.comp_id]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd, cosliceOppositeTwistedArrowMap_right,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion, lift_snd, SSet.comp_const, Equiv.apply_symm_apply]

/-- 表現可能 coslice の錐を、元の終点固定の twisted arrow の全空間へ底上で持ち上げる。 -/
def cosliceToTwistedArrowTarget {C : SSet.{u}} (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTarget c :=
  pullback.lift (cosliceOppositeTwistedArrowMap
    (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)))
    (cosliceOppositeTwistedArrowMap_over c)

/-- 持ち上げた比較は、元の coslice の射影そのものを回収する。 -/
lemma cosliceToTwistedArrowTarget_projection {C : SSet.{u}} (c : C _⦋0⦌) :
    cosliceToTwistedArrowTarget c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetProjection c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)) :=
  pullback.lift_snd _ _ _

/-- 元の coslice から終点固定の全空間への比較も単射。 -/
instance cosliceToTwistedArrowTarget_mono {C : SSet.{u}} (c : C _⦋0⦌) :
    Mono (cosliceToTwistedArrowTarget c) := by
  have : Mono (cosliceOppositeTwistedArrowMap
      (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c))) := by
    unfold cosliceOppositeTwistedArrowMap
    infer_instance
  exact mono_of_mono_fac (pullback.lift_fst _ _ (cosliceOppositeTwistedArrowMap_over c))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
