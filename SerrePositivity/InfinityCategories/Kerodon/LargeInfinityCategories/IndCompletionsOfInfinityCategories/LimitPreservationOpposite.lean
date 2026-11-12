module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedColimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：元の関手の極限保存を、反転と二重反転の同じ全錐に輸送する。
方針：slice 反転の後合成自然性と、二重反転の厳密な自然同型を使う。
規約：元の指定錐を保持し、関手の同値性を要求しない。
使われ方：I-2 d′ の余極限保存の有限生成を極限側へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 指定錐の像の極限性は、反転した同じ余錐の像の余極限性と同値。 -/
lemma map_reverseCocone_isColimit_iff {K X Y : SSet.{u}} {p : K ⟶ X}
    (U : X ⟶ Y) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (SSet.opFunctor.map U) c.reverseCocone) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op _⦋0⦌ :=
    SSet.opObjEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋0⦌ from c)
  exact congrArg (fun f ↦ (f.app (Opposite.op ⦋0⦌) x).val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanSliceOverOpIso_postcomp p U)

/-- 元の形状での保存性は、二重反転した関手にも同じ形状で成立する。 -/
lemma map_isLimit_of_preservation_op_op {K X Y : SSet.{u}}
    (U : X ⟶ Y)
    (hU : ∀ (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c))
    {p : K ⟶ X.op.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (SSet.opFunctor.map (SSet.opFunctor.map U)) c) := by
  let eX := SSet.opFunctorCompOpFunctorIso.app X
  let eY := SSet.opFunctorCompOpFunctorIso.app Y
  have h := (hU _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone eX.hom c) (hc.postcomp_of_isIso eX.hom)).postcomp_of_isIso
    eY.inv
  have hn : eX.hom ≫ U ≫ eY.inv = SSet.opFunctor.map (SSet.opFunctor.map U) := by
    have hn₀ : SSet.opFunctor.map (SSet.opFunctor.map U) ≫ eY.hom = eX.hom ≫ U :=
      SSet.opFunctorCompOpFunctorIso.hom.naturality U
    rw [← Category.assoc, ← hn₀,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).mp h
  change ((c.val ≫ eX.hom) ≫ U) ≫ eY.inv = _
  rw [Category.assoc, Category.assoc, hn]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
