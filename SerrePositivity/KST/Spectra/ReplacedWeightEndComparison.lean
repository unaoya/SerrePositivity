module

public import SerrePositivity.KST.Spectra.LastVertexWeightedEndHomotopy
public import SerrePositivity.KST.Spectra.WeightedEndReedyKan

/-!
概要：Reedy fibrant な係数の置換後の二つの重みの end 比較は全基点 π 同型。
方針：cofibrant な重みから end の Kan 性を構成し、実際のホモトピー逆を π 同型へ送る。
規約：Kan 性の証明も Reedy 条件から得ており、end の Kan 性を別途入力しない。
使われ方：Goerss–Jardine VII §4。通常 Tot 比較の置換後の主比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 係数の Reedy 条件だけから、置換した終頂点の重みの end 比較は全基点 π 同型。 -/
lemma kanWeightPre_piIsomorphism (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    letI := WeightedEndReedyKan.kanComplex
      (CosimplicialKanReplacement.functor.obj stdSimplex.{u}) X
      ReedyWeightCofibrancy.kanStandard hX
    letI := WeightedEndReedyKan.kanComplex
      (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u}) X
      ReedyWeightCofibrancy.kanBousfieldKan hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre
      (Functor.whiskerLeft AsSmall.down kanWeightMap.{u}) (AsSmall.down ⋙ X)) := by
  let := WeightedEndReedyKan.kanComplex
    (CosimplicialKanReplacement.functor.obj stdSimplex.{u}) X
    ReedyWeightCofibrancy.kanStandard hX
  let := WeightedEndReedyKan.kanComplex
    (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u}) X
    ReedyWeightCofibrancy.kanBousfieldKan hX
  exact kanPiIsomorphism_of_qCatEquivalence _
    (kanWeightPre_homotopyEquivalence (AsSmall.down ⋙ X)).isQCatEquivalence

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
