module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanDiscreteLegHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.DiscreteKanConeReadback
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative

/-!
概要：元の native 離散錐の極限性を、同じ元の頂点を持つ全 Kan 脚のホモトピーで検出する。
方針：元の全錐の厳密な読み戻しと、元の豊穣 Hom 比較のホモトピー不変性を組み合わせる。
規約：候補錐を変更せず、脚の厳密な等号や通常の厳密極限性を要求しない。
使われ方：反復積関手の元の評価錐の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の頂点を共有する native 離散全錐の極限性は、元の全 Kan 脚のホモトピーで不変。 -/
lemma discreteSpaceCone_isLimit_iff_of_leg_homotopies {J : Type u}
    (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F))
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (hc : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)
    (hd : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)
    (H : ∀ i, SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg c K hc i) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg d K hd i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanDiscreteCone_isLimit_iff_of_leg_homotopies F K H
  have ec := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteKanConeReadback_eq F c K hc
  have ed := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteKanConeReadback_eq F d K hd
  constructor
  · intro h
    have hcs := (ec ▸ h).cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F).symm
    have hds := he.mp hcs
    exact ed.symm ▸ hds.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
  · intro h
    have hds := (ed ▸ h).cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F).symm
    have hcs := he.mpr hds
    exact ec.symm ▸ hcs.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)

/-- 元の有限錐の全脚が元の反復積の射影にホモトピックなら、元の全錐は極限錐。 -/
lemma finiteSpaceCone_isLimit_of_projection_homotopies (n : ℕ)
    (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n E)))
    (hc : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n E))
    (H : ∀ i, Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg c (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n E) hc i)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ (E j).obj) i.as.down))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply (discreteSpaceCone_isLimit_iff_of_leg_homotopies (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n E) c
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n E) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n E) hc
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_vertex n E) (fun i ↦ ?_)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_isLimit n E)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_kanLeg]
  exact Classical.choice (H i)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
