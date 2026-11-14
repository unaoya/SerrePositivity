module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanReindex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredPointwiseWeakEquivalences
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanAugmentationMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：Over 圏上の coend の図式から元の Bousfield–Kan coend への標準余錐。
方針：忘却関手に沿う添字変更を脚とし、augmentation との可換性を脚で検証する。
規約：比較射の同型性はこの構成には含めない。
使われ方：filtered augmentation の比較を実際の coend 表示へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：各 Over 圏からの忘却は元の coend への余錐を与える。
方針：添字変更の合成則を Over.map と忘却に適用する。
規約：添字の filtered 性は不要。使われ方：標準比較射の構成。 -/
def overBousfieldKanCocone (F : I ⥤ SSet.{u}) : Cocone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F
  ι := {
    app i := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i)
    naturality i j f := by
      change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanMap F f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget j) = _
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex_comp F (Over.forget j) (Over.map f) }

/-- 概要：Over 圏の coend の余極限から元の coend への標準比較。
方針：忘却の余錐を通常の余極限で降下させる。
規約：同型性は別に証明する。使われ方：filtered な coend の表示。 -/
def overBousfieldKanColimitComparison (F : I ⥤ SSet.{u}) :
    colimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  colimit.desc _ (overBousfieldKanCocone F)

/-- 概要：忘却比較の後の augmentation は各段の augmentation と可換。
方針：重み付き脚で第一射影を計算し、元の余錐の自然性を使う。
規約：係数の Kan 性は不要。使われ方：二つの標準比較の整合。 -/
lemma overBousfieldKanReindex_augmentation (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentationMap F i ≫ colimit.ι F i := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro a
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_reindex, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_augmentation,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanι_augmentationMap]
  have h := CartesianMonoidalCategory.whiskerLeft_fst (F.obj a.left)
    (nerveMap (Over.post (Over.forget i).op (X := Opposite.op a)))
  calc
    _ = fst (F.obj a.left) (nerve (Over (Opposite.op a))) ≫ colimit.ι F a.left :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ colimit.ι F a.left) h)
    _ = _ := by
      change _ = fst (F.obj a.left) (nerve (Over (Opposite.op a))) ≫
        F.map a.hom ≫ colimit.ι F i
      exact congrArg (fun t ↦ fst (F.obj a.left) (nerve (Over (Opposite.op a))) ≫ t)
        (colimit.w F a.hom).symm

/-- 概要：余極限からの比較は元の augmentation と厳密に可換。
方針：余極限の全脚で忘却比較の公式を適用する。
規約：任意の通常の小圏の図式。使われ方：filtered augmentation の因子分解。 -/
lemma overBousfieldKanColimitComparison_augmentation (F : I ⥤ SSet.{u}) :
    overBousfieldKanColimitComparison F ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F =
      colim.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentation F) := by
  apply colimit.hom_ext
  intro i
  rw [overBousfieldKanColimitComparison, colimit.ι_desc_assoc, colimit.ι_map]
  exact overBousfieldKanReindex_augmentation F i

/-- 概要：filtered な各段の augmentation の余極限は弱ホモトピー同値。
方針：終対象での弱同値と任意の値の filtered 保存定理を合成する。
規約：元の coend の表示同型はまだ使わない。使われ方：標準比較の二対三則。 -/
lemma overBousfieldKanAugmentation_colimit_isWeakHomotopyEquivalence
    [IsFiltered I] (F : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentation F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise _
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentation_isPointwiseWeakHomotopyEquivalence F)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
