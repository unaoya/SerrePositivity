module

public import SerrePositivity.KST.Spectra.StandardEndKanSequence
public import SerrePositivity.KST.Spectra.WeightedEndStructureMap
public import SerrePositivity.KST.Spectra.KanSequenceAdjointMap

/-!
概要：通常 Tot の列から BK end の列への比較は構造射と厳密に可換。
方針：重みの前合成と係数の後合成の交換、loop 交換の重みへの自然性を使う。
規約：各段の π 同型だけでなく、実際の Kan 列の射を構成する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。通常 Tot と BF homotopy Tot の比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- 重みの比較は end の随伴構造射と厳密に可換。 -/
lemma totalizationComparison_adjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    PointedWeightedEnd.preMap CosimplicialLastVertex.weightMap.{u}
        (levelDiagram (AsSmall.down ⋙ D) n) ≫
      homotopyLimitAdjoint (AsSmall.down ⋙ D) n =
    totalizationAdjoint D n ≫ (ihom PointedSimplicialSet.circle.{u}).map
      (PointedWeightedEnd.preMap CosimplicialLastVertex.weightMap.{u}
        (levelDiagram (AsSmall.down ⋙ D) (n + 1))) := by
  exact PointedWeightedEnd.preMap_adjoint
    (I := AsSmall.{u} SimplexCategory)
    (W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} SimplexCategory))
    (V := AsSmall.down ⋙ stdSimplex.{u})
    CosimplicialLastVertex.weightMap.{u} (AsSmall.down ⋙ D) n

/-- 通常 Tot の標準 end の列から BK end の列への実際の射。 -/
def totalizationComparison (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) :
    Hom (ordinaryTotalization D hD) (homotopyLimit (AsSmall.down ⋙ D)) :=
  Hom.ofAdjoint
    (fun n ↦ PointedWeightedEnd.preMap CosimplicialLastVertex.weightMap.{u}
      (levelDiagram (AsSmall.down ⋙ D) n)) (fun n ↦ by
        rw [ordinaryTotalization_adjoint, homotopyLimit_adjoint]
        exact totalizationComparison_adjoint D n)

/-- 構造射と可換な比較は各段で全基点 π 同型。 -/
lemma totalizationComparison_levelwise (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((totalizationComparison D hD).app n).right := by
  exact PointedTotalization.standardEnd_preMap_piIsomorphism
    (D ⋙ levelEvaluation n) (hD n)

end
end SerrePositivity.KST.Spectra.KanSequence
