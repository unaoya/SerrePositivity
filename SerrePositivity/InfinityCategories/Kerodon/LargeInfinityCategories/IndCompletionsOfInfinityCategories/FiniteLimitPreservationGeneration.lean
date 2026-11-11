module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteColimitPreservationGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LimitPreservationOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FiniteLimitGeneration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.PointConeSpanIso

/-!
概要：空形状と点 cospan の極限保存から、全有限単体集合形状の保存を導く。
方針：二重反転の自然性を保って、全余錐の保存を伴う有限生成を双対化する。
規約：元の指定極限錐の像を結論し、存在だけに弱めない。
使われ方：I-2 d′ の filtered 余極限関手の全有限極限保存。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 空錐と点 cospan の保存から、元の任意の有限形状の極限全錐の保存を得る。 -/
lemma map_isLimit_finite_of_empty_pointCospan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (U : X ⟶ Y)
    (he : ∀ (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c))
    (hs : ∀ (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u}.op ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c))
    {K : SSet.{u}} [K.Finite] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X.op.op := ⟨fun p ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasLimit_iff_postcomp_isIso p (SSet.opFunctorCompOpFunctorIso.app X).hom).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit (X := X) _)⟩
  have hcolim {A : SSet.{u}} [A.Finite] (q : A ⟶ X.op) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_hasLimit_op q).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit _)
  have hE (T : SSet.{u}) (q : (⊥ : T.Subcomplex).toSSet ⟶ X.op) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit (SSet.opFunctor.map U) q := by
    have : ((⊥ : T.Subcomplex) : SSet.{u}).Finite := SSet.finite_of_iso
      ((initialIsInitial (C := SSet.{u})).uniqueUpToIso Subcomplex.isInitialBot)
    obtain ⟨d, hd⟩ := hcolim q
    refine ⟨d, hd, ?_⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff d (SSet.opFunctor.map U)).mp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_of_preservation_op_op U (he T.op)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone d).mp hd
  have hS (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ⟶ X.op) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit (SSet.opFunctor.map U) q := by
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u}.Finite := SSet.finite_of_iso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpanIso.symm
    obtain ⟨d, hd⟩ := hcolim q
    refine ⟨d, hd, ?_⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff d (SSet.opFunctor.map U)).mp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_of_preservation_op_op U hs
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone d).mp hd
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_finite_of_empty_pointSpan (SSet.opFunctor.map U)
    hE hS K.op (SSet.opFunctor.map p)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_reverseCocone_isColimit_iff U c).mp
    (h.map_isColimit c.reverseCocone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone c).mp hc))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
