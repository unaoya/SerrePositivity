module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCosliceEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeColimitReindex

/-!
概要：同値な単射上の余錐を、元の図式と像の余錐を固定して延長する。
方針：相対 coslice 制限の自明 Kan 性の切断で指定頂点を持ち上げる。
規約：余錐の像と制限は raw な射の等式として保つ。
使われ方：標準局所相対余極限を comma fiber へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：同値な単射上の余錐は底の指定余錐を保って延長できる。
方針：部分余錐と底の余錐を相対 coslice の引き戻しの頂点にまとめて持ち上げる。
規約：元の図式 p と像の余錐 b を同時に固定する。
使われ方：局所余錐の添字変更における像の厳密な保存。 -/
lemma exists_kanCocone_extension_over_precompositionEquivalence {A K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (i : A ⟶ K) [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ U))
    (hc : c.val ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ b.val) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, (d.restrict i).val = c.val ∧ d.val ≫ U = b.val := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCosliceRestriction_trivialKanFibration_of_precompositionEquivalence p U hU i hi
  let a : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (i ≫ p) := SSet.yonedaEquiv.symm c
  let f : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ U) := SSet.yonedaEquiv.symm b
  have hcompat : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (i ≫ p) U = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (p ≫ U) i := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    congr 1
    exact Subtype.ext hc
  let t := pullback.lift a f hcompat
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction p U i)
  let l := t ≫ s
  have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction p U i = t := by
    exact (Category.assoc t s (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction p U i)).trans
      ((congrArg (fun r ↦ t ≫ r) hs).trans (Category.comp_id t))
  have hla : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i = a := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (i ≫ p) U)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (p ≫ U) i)) hl
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc, t,
      pullback.lift_fst] using h
  have hlf : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U = f := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (i ≫ p) U)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (p ≫ U) i)) hl
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc, t,
      pullback.lift_snd] using h
  refine ⟨SSet.yonedaEquiv l, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv hla
    rw [SSet.yonedaEquiv_comp] at h
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv l) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm c) at h
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  · have h := congrArg SSet.yonedaEquiv hlf
    rw [SSet.yonedaEquiv_comp] at h
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv l) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm b) at h
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h

/-- 概要：標準の相対余極限余錐も同値な単射に沿って像を固定して延長できる。
方針：余錐を延長し、制限による相対余極限性の保存・反映を適用する。
規約：余錐を独立に選び直さず、指定部分と底の余錐を保つ。
使われ方：局所の相対余極限の存在を comma の局所形へ移す。 -/
lemma exists_kanRelativeColimit_extension_over_precompositionEquivalence
    {A K D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (p : K ⟶ D) (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (i : A ⟶ K) [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ U))
    (hc : c.val ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ b.val)
    (hcol : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U d ∧
      (d.restrict i).val = c.val ∧ d.val ≫ U = b.val := by
  obtain ⟨d, hd, hb⟩ := exists_kanCocone_extension_over_precompositionEquivalence p U hU i hi c b hc
  have he : d.restrict i = c := Subtype.ext hd
  refine ⟨d, ?_, hd, hb⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_iff_restrict_of_precompositionEquivalence U d i hi).2
  rw [he]
  exact hcol

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
