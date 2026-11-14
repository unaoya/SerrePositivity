module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：filtered な Bousfield–Kan augmentation は有限形状からの射を持ち上げる。
方針：射を一段へ因子分解し、その段を重みの恒等頂点で coend に含める。
規約：各段の包含を strict な余錐だとは主張しない。
使われ方：augmentation の弱同値性の有限なデータによる検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：各段を重みの恒等射の頂点で Bousfield–Kan coend に含める。
方針：元の段と Over の恒等対象への定値射の直積を取る。
規約：固定した i ごとの射。使われ方：有限写像の持ち上げ。 -/
def bousfieldKanStage (F : I ⥤ SSet.{u}) (i : I) : F.obj i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  lift (𝟙 (F.obj i))
    (SSet.const (ComposableArrows.mk₀ (Over.mk (𝟙 (Opposite.op i))))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i

/-- 概要：各段からの射と augmentation の合成は元の colimit の脚。
方針：重み付き脚の計算と直積の第一射影。
規約：全ての高次単体での厳密な等式。使われ方：有限因子分解を持ち上げる。 -/
lemma bousfieldKanStage_augmentation (F : I ⥤ SSet.{u}) (i : I) :
    bousfieldKanStage F i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F = colimit.ι F i := by
  rw [bousfieldKanStage, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_augmentation, ← Category.assoc]
  have h : lift (𝟙 (F.obj i))
      (SSet.const (ComposableArrows.mk₀ (Over.mk (𝟙 (Opposite.op i))))) ≫
        fst (F.obj i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op i)) = 𝟙 _ := rfl
  rw [h, Category.id_comp]

/-- 概要：filtered augmentation への有限な試験射は実際に持ち上がる。
方針：有限表示性で一段へ下ろしてから、重みの恒等頂点で coend へ送る。
規約：この存在だけを弱同値性の証明とは数えない。
使われ方：有限ホモトピーの相対持ち上げを構成する第一段階。 -/
lemma bousfieldKanAugmentation_lifts_finite [IsFiltered I]
    (F : I ⥤ SSet.{u}) {K : SSet.{u}} [K.Finite] (b : K ⟶ colimit F) :
    ∃ a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F, a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F = b := by
  obtain ⟨i, f, hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit F) b
  refine ⟨f ≫ bousfieldKanStage F i, ?_⟩
  rw [Category.assoc, bousfieldKanStage_augmentation]
  exact hf

end SerrePositivity.InfinityCategories.Project.FilteredExchange
