module

public import SerrePositivity.KST.Spectra.TotalizationComparisonPi
public import SerrePositivity.KST.Spectra.PointedTotalizationBousfieldKan

/-!
概要：通常の点つき Tot から BK end と点つき enriched end への比較は全基点 π 同型。
方針：基点を保存する既存の比較射を忘却し、通常 Tot 比較と end の厳密同型を使う。
規約：必要な Kan 性も Reedy 条件から供給する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。スペクトルの各段の Tot 比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.PointedTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy 条件から比較の標的の BK end は Kan。 -/
lemma bousfieldKan_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    KanComplex (PointedHomotopyLimit.obj (AsSmall.down ⋙ X)).right := by
  exact CosimplicialTotalization.bousfieldKan_kanComplex
    (X ⋙ PointedSimplicialSet.forget) hX

/-- Reedy 条件の下で、比較の標的の点つき enriched end は Kan。 -/
lemma weightedEnd_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    KanComplex (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).right := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
      ((AsSmall.down ⋙ X) ⋙ PointedSimplicialSet.forget)) :=
    bousfieldKan_kanComplex X hX
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).symm

/-- 基点を保存する通常 Tot の BK 比較は全基点 π 同型。 -/
lemma bousfieldKanComparison_piIsomorphism
    (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    letI := kanComplex X
      ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI := bousfieldKan_kanComplex X hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (bousfieldKanComparison X).right := by
  exact CosimplicialTotalization.bousfieldKanComparison_piIsomorphism
    (X ⋙ PointedSimplicialSet.forget) hX

/-- BF の各段で用いる点つき enriched end への実際の比較も全基点 π 同型。 -/
lemma weightedEndComparison_piIsomorphism
    (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    letI := kanComplex X
      ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI := weightedEnd_kanComplex X hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (weightedEndComparison X).right := by
  let := kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
      ((AsSmall.down ⋙ X) ⋙ PointedSimplicialSet.forget)) :=
    bousfieldKan_kanComplex X hX
  let := weightedEnd_kanComplex X hX
  let := bousfieldKan_kanComplex X hX
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((bousfieldKanComparison X).right ≫
    (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).inv)
  exact (bousfieldKanComparison_piIsomorphism X hX).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).symm)

end
end SerrePositivity.KST.Spectra.PointedTotalization
