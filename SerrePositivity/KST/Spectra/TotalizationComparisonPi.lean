module

public import SerrePositivity.KST.Spectra.OriginalWeightEndComparison
public import SerrePositivity.KST.Spectra.TotalizationWeightedReindex

/-!
概要：Reedy fibrant な余単体単体集合の通常 Tot から BK end への比較は全基点 π 同型。
方針：通常 Tot と標準単体 end の同型を、置換前の重みの比較へ合成する。
規約：Kan 性は係数の Reedy 条件から構成する。
使われ方：Goerss–Jardine VII §4、VIII §1。通常 Tot と homotopy Tot の比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.CosimplicialTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- BK end の Kan 性を元の重みの表示から移す。 -/
lemma bousfieldKan_kanComplex (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (AsSmall.down ⋙ X)) := by
  exact WeightedEndReedyKan.kanComplex BousfieldKanWeightLatching.weight.{u} X
    BousfieldKanWeightLatching.reedyCofibrant hX

/-- 通常 Tot の標準 BK 比較は、Reedy 条件の下で全基点 π 同型。 -/
lemma bousfieldKanComparison_piIsomorphism (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    letI := kanComplex X ((CosimplicialHornFibration.terminal_iff X).mp hX)
    letI := bousfieldKan_kanComplex X hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (bousfieldKanComparison X) := by
  let := kanComplex X ((CosimplicialHornFibration.terminal_iff X).mp hX)
  let := bousfieldKan_kanComplex X hX
  let := WeightedEndReedyKan.kanComplex stdSimplex.{u} X ReedyWeightCofibrancy.standard hX
  rw [bousfieldKanComparison_eq_weightedPre]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso (smallEndIso X)).comp
    (CosimplicialLastVertex.originalWeightPre_piIsomorphism X hX)

end
end SerrePositivity.KST.Spectra.CosimplicialTotalization
