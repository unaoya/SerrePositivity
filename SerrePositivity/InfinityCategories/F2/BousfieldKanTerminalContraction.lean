module

public import SerrePositivity.InfinityCategories.F2.BousfieldKanTerminalCylinderNaturality
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.WeakHomotopyInverse

/-!
概要：終対象を持つ添字の Bousfield–Kan coend は、終対象の値と実際にホモトピー同値。
方針：重みの収縮の円柱を coend 全体へ貼り、指定した section と比較する。
規約：元の図式の Kan 性は不要。
使われ方：filtered 添字をその over 圏の図式で表示する比較の各段。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：重みの折り畳みは augmentation と終対象の段からの section の合成。
方針：coend の全ての脚で段の射の自然性を使う。
規約：実際の単体集合の射の等式。使われ方：円柱の始端の同定。 -/
lemma terminalWeightCollapse_eq_augmentation_section (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    terminalWeightCollapse F ht =
      terminalBousfieldKanAugmentation F ht ≫ terminalWeightStage F ht t := by
  apply weightedColimit_hom_ext
  intro i
  rw [terminalWeightCollapse, weightedColimitι_augmentation,
    terminalBousfieldKanAugmentation, reassoc_of% weightedColimitι_augmentation]
  change _ ≫ terminalWeightStage F ht i = _ ≫ F.map (ht.from i) ≫ terminalWeightStage F ht t
  simp only [← terminalWeightStage_naturality F ht (ht.from i)]

/-- 概要：終対象の値への augmentation は実際の単体的ホモトピー同値。
方針：指定した section は一方の厳密な逆で、他方の合成は重みの収縮で恒等射に結ばれる。
規約：モデル構造や Kan 性を前提としない。使われ方：over 圏の各段の比較。 -/
lemma terminalBousfieldKanAugmentation_isSimplicialHomotopyEquivalence
    (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    IsSimplicialHomotopyEquivalence (terminalBousfieldKanAugmentation F ht) := by
  refine ⟨terminalWeightStage F ht t, ?_, ?_⟩
  · rw [← terminalWeightCollapse_eq_augmentation_section F ht]
    exact ⟨weightedColimitHomotopy (terminalWeightLegHomotopy F ht)
      (terminalWeightLegHomotopy_naturality F ht)⟩
  · rw [terminalWeightStage_augmentation]
    exact ⟨functorHomotopyRefl _⟩

/-- 概要：終対象の値への augmentation は弱ホモトピー同値。
方針：構成した実際のホモトピー逆を全ての Kan 標的で検査する。
規約：元の値の Kan 性は不要。使われ方：filtered な段ごとの模型比較。 -/
lemma terminalBousfieldKanAugmentation_isWeakHomotopyEquivalence
    (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    IsWeakHomotopyEquivalence (terminalBousfieldKanAugmentation F ht) := by
  have h := terminalBousfieldKanAugmentation_isSimplicialHomotopyEquivalence F ht
  exact h.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
