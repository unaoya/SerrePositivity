module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FilteredKanColimits
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FilteredTrivialKanFibrations
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiagramPathReplacement
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiagramPathSpan

/-!
概要：Kan 値の filtered 図式の成分ごとの弱同値は、通常の余極限でも弱同値。
方針：自然な path 置換を二本の自明 Kan fibration の span にし、その余極限を比較する。
規約：各成分で選んだ逆を図式の自然変換と仮定しない。
使われ方：filtered な空間の余極限の具体的な Kan 模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：Kan 値図式の成分ごとの弱同値は filtered 余極限で保存される。
方針：図式全体に自然な path span を作り、余極限の自明 Kan 射影とその切断を使う。
規約：strict な小圏の図式についての主張。使われ方：空間の余極限模型の選択の独立性。 -/
lemma filteredColimitMap_isWeakHomotopyEquivalence
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} [∀ j, KanComplex (F.obj j)] [∀ j, KanComplex (G.obj j)]
    (η : F ⟶ G) (hη : ∀ j, IsWeakHomotopyEquivalence (η.app j)) :
    IsWeakHomotopyEquivalence (colim.map η) := by
  have (j : I) : TrivialKanFibration ((diagramPathProjection η).app j) :=
    inferInstanceAs (TrivialKanFibration (equivalencePathReplacementProjection (η.app j)))
  have (j : I) : TrivialKanFibration ((diagramPathEndpoint η).app j) := by
    have he := (hη j).isSimplicialHomotopyEquivalence.isQCatEquivalence
    exact he.equivalencePathReplacementMap_trivialKanFibration
  have : KanComplex (colim.obj F) := inferInstanceAs (KanComplex (colimit F))
  have : KanComplex (colim.obj G) := inferInstanceAs (KanComplex (colimit G))
  have : Quasicategory (colim.obj (diagramPathReplacement η)) :=
    quasicategory_of_innerFibration (colim.map (diagramPathProjection η))
  have hp := (isQCatEquivalence_of_trivialKanFibration
    (colim.map (diagramPathProjection η))).isWeakHomotopyEquivalence
  have hq := (isQCatEquivalence_of_trivialKanFibration
    (colim.map (diagramPathEndpoint η))).isWeakHomotopyEquivalence
  have hs : IsWeakHomotopyEquivalence (colim.map (diagramPathSection η)) := by
    apply hp.cancel_right
    rw [← CategoryTheory.Functor.map_comp, diagramPathSection_projection,
      CategoryTheory.Functor.map_id]
    exact isWeakHomotopyEquivalence_id _
  have h := hs.comp hq
  simpa only [← CategoryTheory.Functor.map_comp, diagramPathSection_endpoint] using h

end SerrePositivity.InfinityCategories.F2
