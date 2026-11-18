module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedHomIntervalVertices

/-!
概要：反転した全Homの定値頂点が、指定した元の自然変換の反転を表すことを照合する。
方針：区間評価を豊穣Homの作用に戻し、同じ全単体の作用を計算する。
規約：HTT §1.1.5、Kerodon §2.4.3・§3.1の構成の評価法則の特殊化。
  元のHomのKan性を仮定せず、射の方向は変えずに単体の頂点順序を反転する。
使われ方：P3-C1PNの指定した底変換の類の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 全Homの定値頂点から作る反転区間辺の類は、元の反転自然変換の実現の類。 -/
@[cite HTT "1.1.5" (partial := special) "小さい通常の添字圏上の反転したKan値図式の指定自然変換の評価。"]
lemma kanDiagramOppositeHomInterval_natural_hom {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let τ : (F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget ⟶
        (G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget := Functor.whiskerRight η SSet.opFunctor
    Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex ((kanDiagramOppositeHomInterval F G).app _
        (ULift.up (SSet.const (strictDiagramMappingVertex η))))).toTruncated =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) τ).toTruncated := by
  dsimp only
  let D := (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched I).opposite
  let X := edgewiseOrdinaryObject F
  let Y := edgewiseOrdinaryObject G
  let s : (SimplicialCategory.sHom X Y) _⦋0⦌ := SSet.const (strictDiagramMappingVertex η)
  let f := (SimplicialCategory.homEquiv' X Y).symm s
  let τ : (F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget ⟶
      (G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget := Functor.whiskerRight η SSet.opFunctor
  change Truncated.HomotopyCategory.homMk
    (intervalMappingEdgeOfVertex ((kanEnrichedDiagramHomInterval D X Y rfl rfl).app _
      (ULift.up s))).toTruncated = _
  rw [kanEnrichedDiagramHomInterval_vertex_hom]
  apply D.realization_homMk_of_homEquiv f τ
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  funext i
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
