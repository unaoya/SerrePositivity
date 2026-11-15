module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：共同切断実現の元の射作用を、同じ通常の自然変換の辺として読む。
方針：元の豊穣Homの表示をcoherent nerveの辺に送り、同じ実現を後合成する。
規約：別の自然変換を選ばず、指定した豊穣表示の一致を使う。
使われ方：Kerodon §2.4（Tag 00JN）・Corollary 5.6.0.6（Tag 028T）の
実現を用いた、標準引き戻し貼り合わせ射の分類後の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes
namespace TheHomotopyTheoryOfKanComplexes

/-- 概要：元の射の豊穣表示が指定自然変換を表すとき、同じ実現のHom作用も一致する。
方針：通常の射のcoherentな辺の厳密な自然性と、元の端点正規化を使う。
規約：表示の一致を実際の射ごとに検証して使う計算法則で、充満忠実性の仮定ではない。
使われ方：分類された貼り合わせ射を、同じ全単体の切断比較として回収する。 -/
lemma KanEnrichedDiagram.realization_homMk_of_homEquiv
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    {X Y : C} (f : X ⟶ Y)
    (η : D.evaluate X ⋙ kanObjectForget ⟶ D.evaluate Y ⋙ kanObjectForget)
    (h : eHomEquiv SSet.{u} f ≫ D.toEnrichedFunctor.map X Y =
      eHomEquiv SSet.{u} (kanDiagramHom (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨D.evaluate Y, trivial⟩) η)) :
    normalizedVertexHomMap D.realization (D.realization_vertex X).symm
        (D.realization_vertex Y).symm
        (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) =
      Truncated.HomotopyCategory.homMk
        (kanDiagramNaturalTransformationEdge
          (F := ⟨D.evaluate X, trivial⟩) (G := ⟨D.evaluate Y, trivial⟩) η).toTruncated := by
  rw [normalizedVertexHomMap_homMk]
  congr 1
  apply congrArg SSet.Edge.toTruncated
  apply SSet.Edge.ext
  change (kanDiagramRealization J).app (Opposite.op ⦋1⦌)
      ((coherentNerveMap D.toEnrichedFunctor).app (Opposite.op ⦋1⦌)
        (coherentNerveEdge f).edge) =
    (kanDiagramRealization J).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge (kanDiagramHom (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨D.evaluate Y, trivial⟩) η)).edge
  rw [coherentNerveMap_edge_of_homEquiv D.toEnrichedFunctor f (kanDiagramHom (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨D.evaluate Y, trivial⟩) η) h]

end TheHomotopyTheoryOfKanComplexes
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes
