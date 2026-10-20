module

public import SerrePositivity.InfinityCategories.F2.ContinuousKanFilteredUnit
public import SerrePositivity.InfinityCategories.F2.FilteredWeakEquivalences

/-!
概要：任意の単体集合値の filtered 図式の成分ごとの弱同値は余極限でも弱同値。
方針：連続 Kan 置換と単位の余極限で Kan 値図式の場合へ帰着する。
規約：元の値に Kan 性を仮定しない。
使われ方：Over 圏の coend の augmentation を余極限へ送る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered 余極限は任意の単体集合値図式の点ごとの弱同値を保つ。
方針：Q の像の弱同値と二つの単位の余極限に二対三則を使う。
規約：通常の小圏で添字付けた strict 図式。使われ方：非 Kan coend 図式の比較。 -/
lemma filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (hη : ∀ i, IsWeakHomotopyEquivalence (η.app i)) :
    IsWeakHomotopyEquivalence (colim.map η) := by
  have (i : I) : KanComplex ((F ⋙ continuousKanReplacement).obj i) :=
    inferInstanceAs (KanComplex (continuousKanReplacement.obj (F.obj i)))
  have (i : I) : KanComplex ((G ⋙ continuousKanReplacement).obj i) :=
    inferInstanceAs (KanComplex (continuousKanReplacement.obj (G.obj i)))
  have hQ : IsWeakHomotopyEquivalence
      (colim.map (Functor.whiskerRight η continuousKanReplacement)) := by
    apply filteredColimitMap_isWeakHomotopyEquivalence
    intro i
    exact continuousKanReplacement_map_isWeakHomotopyEquivalence _ (hη i)
  have hn : η ≫ continuousKanDiagramUnit G =
      continuousKanDiagramUnit F ≫ Functor.whiskerRight η continuousKanReplacement := by
    apply NatTrans.ext
    funext i
    exact continuousKanReplacementUnit.naturality (η.app i)
  apply (continuousKanDiagramUnit_colimit_isWeakHomotopyEquivalence G).cancel_right
  rw [← CategoryTheory.Functor.map_comp, hn, CategoryTheory.Functor.map_comp]
  exact (continuousKanDiagramUnit_colimit_isWeakHomotopyEquivalence F).comp hQ

end SerrePositivity.InfinityCategories.F2
