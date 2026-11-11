module

public import SerrePositivity.KST.Spectra.PointedTotalizationEndIso

/-!
概要：標準単体の点つき end は Reedy 条件で Kan、終頂点への前合成は全基点 π 同型。
方針：通常 Tot との実際の点つき同型を通じ、構成済みの標準比較の π 同型を使う。
規約：end の Ω 構造を比較するための、前合成そのものについての定理。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。通常 Tot の列と BK end の列の比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.PointedTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準単体の点つき enriched end は Reedy 条件の下で Kan。 -/
lemma standardEnd_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    KanComplex (PointedWeightedEnd.obj
      (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).right := by
  let := kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let e : (obj X).right ≅ (PointedWeightedEnd.obj
      (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).right :=
    PointedSimplicialSet.forget.mapIso (standardEndIso X)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso e

/-- 終頂点の重みの前合成は、点つき enriched end でも全基点 π 同型。 -/
lemma standardEnd_preMap_piIsomorphism
    (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    letI := standardEnd_kanComplex X hX
    letI := weightedEnd_kanComplex X hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedWeightedEnd.preMap
      CosimplicialLastVertex.weightMap (AsSmall.down ⋙ X)).right := by
  let := kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let := standardEnd_kanComplex X hX
  let := weightedEnd_kanComplex X hX
  have he : (standardEndIso X).inv ≫ weightedEndComparison X =
      PointedWeightedEnd.preMap CosimplicialLastVertex.weightMap (AsSmall.down ⋙ X) := by
    rw [weightedEndComparison_eq_preMap, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let e : (PointedWeightedEnd.obj
      (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).right ≅ (obj X).right :=
    PointedSimplicialSet.forget.mapIso (standardEndIso X).symm
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e).comp
      (weightedEndComparison_piIsomorphism X hX)
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((standardEndIso X).inv ≫ weightedEndComparison X).right at h
  rw [he] at h
  exact h

end
end SerrePositivity.KST.Spectra.PointedTotalization
