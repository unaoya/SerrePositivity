module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoCurryComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonPrecomposition

/-!
概要：元の通常のKan値自然変換のcoherent実現が、指定した合成を保つことを照合する。
方針：同じcoherent合成三角形を実現し、既存の正規化Hom作用の合成則を使う。
規約：HTT §1.1.5、Kerodon §2.4.3・Remark 3.1.6.3（Tag 01YZ）の構成の法則。
  元の図式全体の射を比較する特殊化で、点ごとの像の一致だけを仮定しない。
使われ方：5∞-1のP3-C1PNで、元の共同切断比較の値の類を合成・相殺する。
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


namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 元の自然変換の実現の類は、同じ辺を実現して端点を揃えたHom作用。 -/
lemma kanDiagramNaturalTransformationHom_eq_normalized {I : Type u} [Category.{u} I]
    {F G : KanDiagramObject I} (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated =
      normalizedVertexHomMap (kanDiagramRealization I) (kanDiagramRealization_vertex F).symm
        (kanDiagramRealization_vertex G).symm
        (Truncated.HomotopyCategory.homMk (coherentNerveEdge (kanDiagramHom η)).toTruncated) :=
  (normalizedVertexHomMap_homMk (kanDiagramRealization I)
    (kanDiagramRealization_vertex F).symm (kanDiagramRealization_vertex G).symm
    (coherentNerveEdge (kanDiagramHom η))).symm

/-- 元の自然変換の合成は、同じcoherent実現の全図式の射の合成へ写る。 -/
@[cite HTT "1.1.5" (partial := special) "通常の小さい添字圏上のKan値自然変換のcoherent実現の合成則。"]
lemma kanDiagramNaturalTransformationHom_comp {I : Type u} [Category.{u} I]
    {F G H : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ H.val ⋙ kanObjectForget) :
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (η ≫ θ)).toTruncated =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
        Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge θ).toTruncated := by
  have hc : kanDiagramHom (η ≫ θ) = kanDiagramHom η ≫ kanDiagramHom θ := by
    rfl
  rw [kanDiagramNaturalTransformationHom_eq_normalized, kanDiagramNaturalTransformationHom_eq_normalized η, kanDiagramNaturalTransformationHom_eq_normalized θ,
    ← normalizedVertexHomMap_hom_comp, hc]
  congr 1
  exact (Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (kanDiagramHom η) (kanDiagramHom θ)).toTruncated).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
