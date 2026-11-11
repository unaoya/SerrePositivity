module

public import SerrePositivity.KST.Spectra.ReedyWeightRestrictionLifting
public import SerrePositivity.KST.Spectra.ReplacedWeightEndComparison

/-!
概要：Reedy 置換前の終頂点の重みの end 比較は全基点 π 同型。
方針：置換単位による制限の全単射 RLP から切断を作り、置換後の比較の π 同型を移送する。
規約：end の非空性を仮定せず、切断は初期対象からの持ち上げで得る。
使われ方：Goerss–Jardine VII §4、VIII §1。通常 Tot 比較の置換前への移送。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy 条件の下で、置換前の終頂点の重みへの制限は全基点 π 同型。 -/
lemma originalWeightPre_piIsomorphism (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp (terminal.from X)) :
    letI := WeightedEndReedyKan.kanComplex stdSimplex.{u} X ReedyWeightCofibrancy.standard hX
    letI := WeightedEndReedyKan.kanComplex BousfieldKanWeightLatching.weight.{u} X
      BousfieldKanWeightLatching.reedyCofibrant hX
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre
      (Functor.whiskerLeft AsSmall.down cosimplicialMap.{u}) (AsSmall.down ⋙ X)) := by
  let := WeightedEndReedyKan.kanComplex stdSimplex.{u} X ReedyWeightCofibrancy.standard hX
  let := WeightedEndReedyKan.kanComplex BousfieldKanWeightLatching.weight.{u} X
    BousfieldKanWeightLatching.reedyCofibrant hX
  let := WeightedEndReedyKan.kanComplex (CosimplicialKanReplacement.functor.obj stdSimplex.{u}) X
    ReedyWeightCofibrancy.kanStandard hX
  let := WeightedEndReedyKan.kanComplex
    (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u}) X
    ReedyWeightCofibrancy.kanBousfieldKan hX
  let a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ CosimplicialKanReplacement.functor.obj
      stdSimplex.{u}) (AsSmall.down ⋙ X) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ stdSimplex.{u}) (AsSmall.down ⋙ X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down
    (CosimplicialKanReplacement.unit.app stdSimplex.{u})) (AsSmall.down ⋙ X)
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ CosimplicialKanReplacement.functor.obj
      BousfieldKanWeightLatching.weight.{u}) (AsSmall.down ⋙ X) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ BousfieldKanWeightLatching.weight.{u})
        (AsSmall.down ⋙ X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down
    (CosimplicialKanReplacement.unit.app BousfieldKanWeightLatching.weight.{u})) (AsSmall.down ⋙ X)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down kanWeightMap.{u})
    (AsSmall.down ⋙ X)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down cosimplicialMap.{u})
    (AsSmall.down ⋙ X)
  have ha : (MorphismProperty.monomorphisms SSet.{u}).rlp a :=
    ReedyWeightRestrictionLifting.rlp_monomorphisms _
      (CosimplicialKanReplacement.unit_reedy_anodyne _) X hX
  have hb : (MorphismProperty.monomorphisms SSet.{u}).rlp b :=
    ReedyWeightRestrictionLifting.rlp_monomorphisms _
      (CosimplicialKanReplacement.unit_reedy_anodyne _) X hX
  have haπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight a ha
  have hbπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight b hb
  have hfπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := kanWeightPre_piIsomorphism X hX
  have hw : Functor.whiskerLeft AsSmall.down
        (CosimplicialKanReplacement.unit.app BousfieldKanWeightLatching.weight.{u}) ≫
        Functor.whiskerLeft AsSmall.down kanWeightMap.{u} =
      Functor.whiskerLeft AsSmall.down cosimplicialMap.{u} ≫
        Functor.whiskerLeft AsSmall.down (CosimplicialKanReplacement.unit.app stdSimplex.{u}) := by
    apply NatTrans.ext
    funext j
    exact (NatTrans.congr_app (CosimplicialKanReplacement.unit.naturality cosimplicialMap)
      (AsSmall.down.obj j)).symm
  have he : f ≫ b = a ≫ g := by
    dsimp only [f, b, a, g]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, hw]
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration a := ⟨ha⟩
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section a
  have hsπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism s := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    (by rw [hs]; exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _) haπ
  have hπ := hsπ.comp (hfπ.comp hbπ)
  have he' : s ≫ (f ≫ b) = g := by rw [he, ← Category.assoc, hs, Category.id_comp]
  rw [he'] at hπ
  exact hπ

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
