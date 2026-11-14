module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanFilteredAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OppositeWeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitOpposite
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitOppositeAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：N の反転重みの coend の filtered augmentation は弱ホモトピー同値。
方針：coend の反転比較と二重反転の係数同型で通常の重みの場合から移す。
規約：元の単体集合値の Kan 性は不要。
使われ方：通常の filtered colimit と native な余極限模型の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]
local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：反転後の図式の augmentation は元の augmentation の弱同値性を継ぐ。
方針：coend と colimit の反転同型の可換性に二対三則を使う。
規約：一般の反変重み。使われ方：反転した BK 重みへの帰着。 -/
lemma weightedColimitAugmentation_op_isWeakHomotopyEquivalence
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W (colimit.cocone F))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (W ⋙ SSet.opFunctor) (colimit.cocone (F ⋙ SSet.opFunctor))) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite.weightedColimitOppositeIso W F))
  apply he.isWeakHomotopyEquivalence.cancel_left
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation_op_factor]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (preservesColimitIso SSet.opFunctor F)
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence _ h).comp hc.isWeakHomotopyEquivalence

/-- 概要：反転重みの coend から通常の余極限への標準 augmentation。
方針：反転重みの変数を忘れて余錐の脚に送る。
規約：N の reflectedBousfieldKanColimit が始域。使われ方：native な模型との比較。 -/
def reflectedBousfieldKanAugmentation (F : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit F ⟶ colimit F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (colimit.cocone F)

/-- 概要：通常の filtered 図式の反転 BK augmentation は弱ホモトピー同値。
方針：係数の反転に通常の定理を適用し、二重反転の自然同型で元に戻す。
規約：元の図式の値に Kan 性は不要。使われ方：N の Kan coend からの比較。 -/
lemma reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered
    [IsFiltered I] (F : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (reflectedBousfieldKanAugmentation F) := by
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor
  let e : (F ⋙ SSet.opFunctor) ⋙ SSet.opFunctor ≅ F :=
    Functor.isoWhiskerLeft F SSet.opFunctorCompOpFunctorIso ≪≫ Functor.rightUnitor F
  have hd := weightedColimitAugmentation_op_isWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (F ⋙ SSet.opFunctor)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered _)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitFunctor W).mapIso e)
  apply he.isWeakHomotopyEquivalence.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap W e.hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W (colimit.cocone F))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation_naturality W e.hom _ _ (colim.map e.hom)
    (fun i ↦ colimit.ι_map e.hom i)]
  exact hd.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (colim.mapIso e)).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.FilteredExchange
