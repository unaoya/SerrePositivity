module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanAugmentationMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：各 Over 圏の augmentation は元の図式への自然変換を成す。
方針：全ての重み付き脚で Over の構造射と元の係数の合成を比較する。
規約：成分で選んだ逆の自然性を仮定しない。
使われ方：filtered 余極限へ送る成分ごとの弱同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：各 Over 圏の augmentation は Over の後合成と可換。
方針：普遍脚上で重みの変数を忘れ、元の F の合成保存を使う。
規約：指定された係数の射そのものを使う。使われ方：自然変換の構成。 -/
lemma overBousfieldKanAugmentationMap_naturality (F : I ⥤ SSet.{u})
    {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanMap F f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentationMap F j =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentationMap F i ≫ F.map f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro a
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanι_map,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanι_augmentationMap, reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanι_augmentationMap]
  change (F.obj a.left ◁ nerveMap (Over.post (Over.map f).op (X := Opposite.op a))) ≫
    fst (F.obj a.left) (nerve (Over (Opposite.op ((Over.map f).obj a)))) ≫
      F.map (a.hom ≫ f) =
    fst (F.obj a.left) (nerve (Over (Opposite.op a))) ≫ F.map a.hom ≫ F.map f
  have h := CartesianMonoidalCategory.whiskerLeft_fst (F.obj a.left)
    (nerveMap (Over.post (Over.map f).op (X := Opposite.op a)))
  calc
    _ = fst (F.obj a.left) (nerve (Over (Opposite.op a))) ≫ F.map (a.hom ≫ f) :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ F.map (a.hom ≫ f)) h)
    _ = _ := by simp only [F.map_comp]

/-- 概要：Over 圏上の coend の図式から元の係数図式への自然な augmentation。
方針：終対象での各 augmentation とその厳密な自然性を束ねる。
規約：F の値に Kan 性は不要。使われ方：各段の弱同値を余極限へ送る。 -/
def overBousfieldKanAugmentation (F : I ⥤ SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F ⟶ F where
  app i := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentationMap F i
  naturality _ _ f := overBousfieldKanAugmentationMap_naturality F f

/-- 概要：図式の augmentation は全ての成分で弱ホモトピー同値。
方針：各 Over 圏の終対象による構成済みの収縮を使う。
規約：逆を成分ごとに自然変換とみなさない。使われ方：Kan 置換後の比較。 -/
lemma overBousfieldKanAugmentation_isPointwiseWeakHomotopyEquivalence
    (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((overBousfieldKanAugmentation F).app i) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentationMap_isWeakHomotopyEquivalence F i

end SerrePositivity.InfinityCategories.Project.FilteredExchange
