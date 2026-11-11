module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanWeightPost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitReindexNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitWeightMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：任意の添字関手に沿う Bousfield–Kan coend の標準比較射。
方針：Over.post の重みの比較を作用させてから coend の添字を変更する。
規約：図式の係数と重みの比較を両方保持する。
使われ方：Over.map に沿う各段の coend の関手的な構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I J K : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory K]

/-- 概要：制限した図式の Bousfield–Kan coend を元の coend へ送る。
方針：反対関手により誘導された重みの変更と coend の添字変更を合成する。
規約：U の cofinality は不要。使われ方：over 圏の構造射と忘却射。 -/
def bousfieldKanReindex (F : I ⥤ SSet.{u}) (U : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (U ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost U.op) (U ⋙ F) ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F U

/-- 概要：添字変更後の普遍脚は Over.post の nerve を重みに作用させた元の脚。
方針：重みと添字の二段の変更の脚の公式を使う。
規約：全ての重みの高次単体での等式。使われ方：関手性と augmentation の検証。 -/
lemma bousfieldKanι_reindex (F : I ⥤ SSet.{u}) (U : J ⥤ I) (j : J) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Jᵒᵖ) (U ⋙ F) j ≫ bousfieldKanReindex F U =
      (F.obj (U.obj j) ◁ nerveMap (Over.post U.op (X := Opposite.op j))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F (U.obj j) := by
  rw [bousfieldKanReindex, reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_weightMap,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_reindex]
  rfl

/-- 概要：恒等の添字変更は恒等射。
方針：重みの比較と coend の添字変更の単位則を合成する。
規約：元の図式を保持する。使われ方：Over の図式の恒等則。 -/
lemma bousfieldKanReindex_id (F : I ⥤ SSet.{u}) :
    bousfieldKanReindex F (𝟭 I) = 𝟙 _ := by
  change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost (𝟭 Iᵒᵖ)) F ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F (𝟭 I) = 𝟙 _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost_id, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap_id, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex_id,
    Category.id_comp]

/-- 概要：二段の Bousfield–Kan 添字変更は合成関手による比較射。
方針：重み変更と添字変更を交換し、それぞれの合成則を使う。
規約：先に V、次に U。使われ方：Over.map に沿う図式の合成則。 -/
lemma bousfieldKanReindex_comp (F : I ⥤ SSet.{u}) (U : J ⥤ I) (V : K ⥤ J) :
    bousfieldKanReindex (U ⋙ F) V ≫ bousfieldKanReindex F U =
      bousfieldKanReindex F (V ⋙ U) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindexWeightMap_comp F U V
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost U.op) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost V.op)
  simpa only [bousfieldKanReindex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightPost_comp] using! h

/-- 概要：等しい添字関手は、始域の等式による輸送を含めて同じ比較射を与える。
方針：関手の等式で場合分けする。
規約：coend の始域の依存性を明示する。使われ方：Over の関手則の移送。 -/
lemma bousfieldKanReindex_congr (F : I ⥤ SSet.{u}) {U V : J ⥤ I} (h : U = V) :
    eqToHom (congrArg (fun L ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (L ⋙ F)) h) ≫
      bousfieldKanReindex F V = bousfieldKanReindex F U := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
