module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalCylinder
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalWeight
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalWeightNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：終対象による coend の脚上の円柱は dinatural。
方針：重みの収縮の自然性、tensor の交換則、普遍脚の dinaturality を組み合わせる。
規約：全ての高次単体を同時に比較する。
使われ方：脚上のホモトピーを coend 全体へ降下させる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：終対象からの収縮円柱は coend の同一視と整合する。
方針：結合子で時間を移し、重みの自然性の後に coend の関係を使う。
規約：元の円柱を変更しない。使われ方：global な収縮ホモトピーの構成。 -/
lemma terminalWeightLegHomotopy_naturality (F : I ⥤ SSet.{u}) (ht : IsTerminal t)
    {i j : I} (f : i ⟶ j) :
    ((F.obj i ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).map f.op) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightLegHomotopy F ht i).h =
        ((F.map f ▷ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightLegHomotopy F ht j).h := by
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ
  change ((F.obj i ◁ W.map f.op) ▷ (Δ[1] : SSet.{u})) ≫
    (α_ (F.obj i) (W.obj (Opposite.op i)) (Δ[1] : SSet.{u})).hom ≫
      (F.obj i ◁ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy ht i).h) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i =
    ((F.map f ▷ W.obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj j) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
        (F.obj j ◁ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy ht j).h) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F j
  have h₁ : ((F.obj i ◁ W.map f.op) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj i) (W.obj (Opposite.op i)) (Δ[1] : SSet.{u})).hom =
        (α_ (F.obj i) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
          (F.obj i ◁ (W.map f.op ▷ (Δ[1] : SSet.{u}))) := rfl
  have h₂ : ((F.map f ▷ W.obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj j) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom =
        (α_ (F.obj i) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
          (F.map f ▷ (W.obj (Opposite.op j) ⊗ (Δ[1] : SSet.{u}))) := rfl
  rw [reassoc_of% h₁, reassoc_of% h₂, ← whiskerLeft_comp_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy_naturality, whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
