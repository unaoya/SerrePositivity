module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanTerminalStages
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanTerminalWeight
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：終対象への射による coend 内の余錐と、その折り畳みから恒等への脚上の円柱。
方針：各重みの始対象からの収縮を元の図式の値と tensor する。
規約：円柱の射を全ての脚で実際に構成する。
使われ方：terminal augmentation のホモトピー逆の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：指定した重みの頂点での段の射を strict な余錐に束ねる。
方針：証明した段の射の自然性を使う。
規約：頂点は元の coend。使われ方：coend の折り畳み。 -/
def terminalWeightCocone (F : I ⥤ SSet.{u}) (ht : IsTerminal t) : Cocone F where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F
  ι := { app i := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightStage F ht i
         naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightStage_naturality F ht f }

/-- 概要：重みを指定された頂点へ潰す coend の自己射。
方針：指定頂点からの strict な余錐への augmentation を使う。
規約：元の coend の射。使われ方：恒等射への収縮の始点。 -/
def terminalWeightCollapse (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (terminalWeightCocone F ht)

/-- 概要：各重み付き脚の上で、折り畳みを元の脚へ結ぶ実際のホモトピー。
方針：重みの収縮の円柱を元の段と tensor して、coend の普遍脚を続ける。
規約：図式の Kan 性は不要。使われ方：coend 全体へのホモトピーの貼り合わせ。 -/
def terminalWeightLegHomotopy (F : I ⥤ SSet.{u}) (ht : IsTerminal t) (i : I) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i ≫ terminalWeightCollapse F ht)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i ≫ 𝟙 _) where
  h := (α_ (F.obj i) (nerve (Over (Opposite.op i))) (Δ[1] : SSet.{u})).hom ≫
    (F.obj i ◁ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy ht i).h) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i
  h₀ := by
    change SSet.ι₀ ≫ _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι _ F i ≫ terminalWeightCollapse F ht
    have h : SSet.ι₀ (X := F.obj i ⊗ nerve (Over (Opposite.op i))) ≫
        (α_ (F.obj i) (nerve (Over (Opposite.op i))) (Δ[1] : SSet.{u})).hom =
          (F.obj i ◁ SSet.ι₀) := rfl
    rw [← Category.assoc, h, ← whiskerLeft_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy ht i).h₀]
    rw [terminalWeightCollapse, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι _ F i ≫ 𝟙 _
    have h : SSet.ι₁ (X := F.obj i ⊗ nerve (Over (Opposite.op i))) ≫
        (α_ (F.obj i) (nerve (Over (Opposite.op i))) (Δ[1] : SSet.{u})).hom =
          (F.obj i ◁ SSet.ι₁) := rfl
    rw [← Category.assoc, h, ← whiskerLeft_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightHomotopy ht i).h₁]
    simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
