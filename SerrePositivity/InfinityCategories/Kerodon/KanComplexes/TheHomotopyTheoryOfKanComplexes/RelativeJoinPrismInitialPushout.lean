module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCoverage
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：prism の初期部分 Z(0) を境界 prism と終端の pushout として表す。
方針：終端の自然性の pullback、二つの像の被覆、包含の単射性を使う。
規約：通常の単体集合の pushout の構成。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱側の比較の立方体の前面。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：境界の prism の Z(0) への標準包含。
方針：初期部分の左の生成部分の像へ射を制限する。
規約：区間は左因子。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、初期部分の pushout の一つ目の射。 -/
noncomputable def relativeJoinPrismInitialBoundary (m : ℕ) :
    (Δ[1] : SSet.{u}) ⊗ (boundary m : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m :=
  Subcomplex.lift ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) le_sup_left

/-- 概要：prism の終端の Z(0) への標準包含。
方針：初期部分の右の生成部分の像へ射を制限する。
規約：係数は標準 m 単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、初期部分の pushout の二つ目の射。 -/
noncomputable def relativeJoinPrismInitialEndpoint (m : ℕ) :
    (Δ[m] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) le_sup_right

/-- 概要：境界 prism と終端はその共通の終端に沿って Z(0) を作る。
方針：終端の自然性の pullback を像の和の pushout に変える。
規約：貼り合わせ部分は標準 m 単体の境界。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱の比較の前面の構成。 -/
@[kerodon 00TH]
lemma relativeJoinPrismInitial_isPushout (m : ℕ) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) (boundary m).ι
      (relativeJoinPrismInitialBoundary m) (relativeJoinPrismInitialEndpoint m) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_prismEndpoint_naturality 1 (boundary.{u} m).ι
  apply IsPushout.of_forall_isPushout_app
  intro n
  have : Mono ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) := (tensorLeft _).map_mono _
  apply Types.isPushout_of_isPullback_of_mono (hp.app n)
    (k := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι.app n)
  · exact congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ (boundary m : SSet.{u}) ⟶
      (Δ[1] : SSet.{u}) ⊗ Δ[m] ↦ k.app n) (Subcomplex.lift_ι _ _)
  · exact congrArg (fun k : (Δ[m] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[m] ↦
      k.app n) (Subcomplex.lift_ι _ _)
  · apply Set.eq_univ_of_forall
    intro z
    rcases z.property with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, Subtype.ext hx⟩
    · exact Or.inr ⟨y, Subtype.ext hy⟩
  · intro x y _ _ h
    exact (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[m] : SSet.{u})).app n)).mp inferInstance h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
