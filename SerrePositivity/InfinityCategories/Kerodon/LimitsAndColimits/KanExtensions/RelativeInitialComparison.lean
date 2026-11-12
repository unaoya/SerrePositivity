module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：充満忠実な比較を用いた相対始対象性の移送。
方針：写像空間の可換な比較で同値を合成・消去し、頂点の全射性で全ての終点を回収する。
規約：比較関手の厳密な可換性と頂点上の全射性を明示する。
使われ方：通常の coslice と固定図式の余錐の族の相対普遍性の同定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：可換な充満忠実比較で相対始対象性を同定できる。
方針：一方の方向では後合成の同値を消し、逆方向では頂点の全射性で終点を持ち上げる。
規約：始域側の比較 a は頂点で全射、標的側の比較 b は充満忠実ならよい。
使われ方：相対余極限の二つの余錐圏の模型の比較。 -/
lemma kanRelativeInitialVertex_iff_of_comparison {S T X Y : SSet.{u}}
    [Quasicategory S] [Quasicategory T] [Quasicategory X] [Quasicategory Y]
    (f : S ⟶ T) (g : X ⟶ Y) (a : S ⟶ X) (b : T ⟶ Y)
    (h : a ≫ g = f ≫ b) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful b)
    (hs : Function.Surjective (a.app (Opposite.op ⦋0⦌))) (x : S _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex f x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex g (a.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · intro hx y
    obtain ⟨z, rfl⟩ := hs y
    have he := (hx z).comp (hb _ _)
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he
    have hh := congrArg (fun k : S ⟶ Y ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap k x z)) h
    have he' := hh.mpr he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he'
    exact (ha x z).cancel_left he'
  · intro hx z
    have he := (ha x z).comp (hx _)
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he
    have hh := congrArg (fun k : S ⟶ Y ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap k x z)) h
    have he' := hh.mp he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he'
    exact (hb _ _).cancel_right he'

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
