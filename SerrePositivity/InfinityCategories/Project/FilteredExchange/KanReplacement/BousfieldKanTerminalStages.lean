module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalWeight
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanTerminalWeightNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：終対象への射で選んだ重みの頂点から、coend 内の strict な余錐を構成する。
方針：選んだ頂点の自然性を coend の dinaturality へ代入する。
規約：恒等頂点での各段の包含とは区別する。
使われ方：terminal な添字の augmentation の収縮の始端。
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

/-- 概要：終対象への射を表す重みの頂点で各段を coend に送る。
方針：元の段と指定頂点への定値射を直積して普遍脚を続ける。
規約：終対象 t とその普遍性を固定する。使われ方：収縮の section。 -/
def terminalWeightStage (F : I ⥤ SSet.{u}) (ht : IsTerminal t) (i : I) :
    F.obj i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  lift (𝟙 _) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht i))) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i

/-- 概要：指定頂点での段の射は元の図式に対して strict な余錐を作る。
方針：頂点の自然性を普遍脚の dinaturality に代入する。
規約：coend の全ての単体での等式。使われ方：各段から終対象の段への因子分解。 -/
lemma terminalWeightStage_naturality (F : I ⥤ SSet.{u}) (ht : IsTerminal t)
    {i j : I} (f : i ⟶ j) : F.map f ≫ terminalWeightStage F ht j = terminalWeightStage F ht i := by
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ
  have hv : (W.map f.op).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht j)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht i) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((Over.map f.op).obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht j)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint_map ht f]
  let l := lift (𝟙 (F.obj i)) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht j)))
  have h₁ : l ≫ (F.obj i ◁ W.map f.op) =
      lift (𝟙 _) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht i))) := by
    apply CartesianMonoidalCategory.hom_ext
    · rfl
    · change (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht j)) :
        F.obj i ⟶ W.obj (Opposite.op j)) ≫ W.map f.op =
          SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht i))
      simpa only [SSet.const_comp] using! congrArg
        (fun x ↦ (SSet.const x : F.obj i ⟶ W.obj (Opposite.op i))) hv
  have h₂ : l ≫ (F.map f ▷ W.obj (Opposite.op j)) =
      F.map f ≫ lift (𝟙 _) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalWeightPoint ht j))) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  have h := congrArg (fun q ↦ l ≫ q) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition W F f)
  rw [← Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc] at h
  exact h.symm

/-- 概要：終対象の値を頂点とする通常の余錐。
方針：終対象への一意な射を F で送る。
規約：元の F の構造射そのものを脚にする。使われ方：terminal augmentation の標的。 -/
def terminalIndexCocone (F : I ⥤ SSet.{u}) (ht : IsTerminal t) : Cocone F where
  pt := F.obj t
  ι :=
    { app i := F.map (ht.from i)
      naturality i j f := by
        change F.map f ≫ F.map (ht.from j) = F.map (ht.from i)
        rw [← F.map_comp, ht.hom_ext (f ≫ ht.from j) (ht.from i)] }

/-- 概要：終対象の値への augmentation。
方針：終対象の値を頂点とする通常の余錐への比較を使う。
規約：Kan 性は不要。使われ方：terminal な coend のホモトピー同値。 -/
def terminalBousfieldKanAugmentation (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F ⟶ F.obj t :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (terminalIndexCocone F ht)

/-- 概要：終対象の段からの section と augmentation の合成は恒等射。
方針：重みを忘れてから終対象の自己射の一意性を使う。
規約：ホモトピーまでではなく厳密な等式。使われ方：ホモトピー逆の一方。 -/
lemma terminalWeightStage_augmentation (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    terminalWeightStage F ht t ≫ terminalBousfieldKanAugmentation F ht = 𝟙 _ := by
  rw [terminalWeightStage, terminalBousfieldKanAugmentation, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation, ← Category.assoc]
  change F.map (ht.from t) = 𝟙 _
  rw [ht.hom_ext (ht.from t) (𝟙 t), F.map_id]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
