module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanFilteredUnit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakEquivalences
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の単体集合値の filtered 図式の成分ごとの弱同値は余極限でも弱同値。
方針：連続 Kan 置換と単位の余極限で Kan 値図式の場合へ帰着する。
規約：元の値に Kan 性を仮定しない。
使われ方：Over 圏の coend の augmentation を余極限へ送る。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 概要：filtered 余極限は任意の単体集合値図式の点ごとの弱同値を保つ。
方針：Q の像の弱同値と二つの単位の余極限に二対三則を使う。
規約：通常の小圏で添字付けた strict 図式。使われ方：非 Kan coend 図式の比較。 -/
@[kerodon 00XE]
lemma filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map η) := by
  have (i : I) : KanComplex ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj i) :=
    inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (F.obj i)))
  have (i : I) : KanComplex ((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj i) :=
    inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (G.obj i)))
  have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (colim.map (Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.filteredColimitMap_isWeakHomotopyEquivalence
    intro i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence _ (hη i)
  have hn : η ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanDiagramUnit G =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanDiagramUnit F ≫ Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement := by
    apply NatTrans.ext
    funext i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality (η.app i)
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanDiagramUnit_colimit_isWeakHomotopyEquivalence G).cancel_right
  rw [← CategoryTheory.Functor.map_comp, hn, CategoryTheory.Functor.map_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanDiagramUnit_colimit_isWeakHomotopyEquivalence F).comp hQ

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
