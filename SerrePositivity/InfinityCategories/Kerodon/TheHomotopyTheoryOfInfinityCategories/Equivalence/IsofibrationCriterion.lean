module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PathReplacementLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyPathParameters
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：圏論的同値の右持ち上げと inner fibration・可逆辺の持ち上げの同値。
方針：前合成同値で仮の延長を選び、逆向きの可逆 path を境界固定で持ち上げる。
規約：モデル圏の因子分解や追加公理を使わない。
使われ方：標準 isofibration の条件を相対 Kan 構成の右持ち上げ条件へ接続する。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：inner fibration で可逆辺を持ち上げられる射は単射な前合成同値を右に持ち上げる。
方針：仮の延長と標的図式を指定部分で定値な可逆 path で結び、終点指定で持ち上げる。
規約：元・標的は quasicategory、可逆辺の持ち上げは終点と像を厳密に保つ。
使われ方：isofibration 上での相対 Kan 拡張の組み立て。 -/
@[kerodon 01FR]
lemma equivalenceLifting_of_innerFibration_of_targetLifting
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U := by
  intro A B i hm hi
  have : Mono i := hm
  constructor
  intro a b sq
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pre_surjective_of_essentiallySurjective i
    (hi D).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  obtain ⟨c, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B D).surjective v
  have hc : i ≫ c = a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A D).injective hv
  obtain ⟨P, hPi, hP₀, hP₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_kanEquivalencePath_extension i hi
    (a ≫ U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl E) b (c ≫ U)
    (by simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]; exact sq.w)
    (by simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]
        rw [← Category.assoc, hc])
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration U hU
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt U 1) i inferInstance
  let t : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathTargetAt U 1 := pullback.lift P c hP₁
  let s : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl D) i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt U 1) t := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalencePathRefl_map, t, pullback.lift_fst]
      exact hPi.symm
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id, t, pullback.lift_snd]
      exact hc.symm
  have hsP : s.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap U = P := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst U 1, ← Category.assoc, s.fac_right]
    exact pullback.lift_fst _ _ _
  refine CommSq.HasLift.mk' {
    l := s.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 0
    fac_left := ?_
    fac_right := ?_ }
  · rw [← Category.assoc, s.fac_left, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint,
      Category.comp_id]
  · rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc, hsP, hP₀]

/-- 概要：quasicategory 間では圏論的同値の右持ち上げは isofibration の二条件と同値。
方針：内ホーンと可逆区間への適用、および相対 path による逆向きの構成を合わせる。
規約：可逆辺の持ち上げは終点指定の向きで述べる。
使われ方：標準の inner 性と同型持ち上げを相対 Kan 図式の公開入力に使う。 -/
@[kerodon 01EV, kerodon 01FR]
lemma equivalenceLifting_iff_inner_and_invertibleTargetLifting
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U ↔ InnerFibration U ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting U := by
  constructor
  · intro hU
    exact ⟨hU.innerFibration, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting hU⟩
  · rintro ⟨hinner, htarget⟩
    have : InnerFibration U := hinner
    intro A B i hm hi
    exact equivalenceLifting_of_innerFibration_of_targetLifting U htarget i hm hi

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
