module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.DiscreteConeEdgeReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.RepresentableLimitEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg

/-!
概要：元の離散空間値錐を、元の全 Kan 脚を持つ通常の錐から厳密に回収する。
方針：元の頂点と脚を読み戻し、離散全錐の一意性で strict 表示を同定する。
規約：元の全錐を等式で保持。通常の錐の極限性を元の native 錐へ反映する。
使われ方：有限 coherent 積の評価錐の点ごとの極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {J : Type u} (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F))
  (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (hc : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)

/-- 元の native 錐の全脚をそのまま戻した、元の Kan 対象を頂点とする通常の錐。 -/
def discreteKanConeReadback : Cone F where
  pt := K
  π := Discrete.natTrans (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg c K hc i)

/-- 元の native 全錐は、元の全 Kan 脚を持つ通常の錐の strict 表示そのもの。 -/
lemma discreteKanConeReadback_eq : c =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (discreteKanConeReadback F c K hc)).cast
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteCone_ext_of_vertex_leg
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
    exact hc
  · intro j
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (ULift.up (ComposableArrows.mk₀ (Discrete.mk j)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (discreteKanConeReadback F c K hc))
        (ULift.up (ComposableArrows.mk₀ (Discrete.mk j)))).edge
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge c K hc (Discrete.mk j)).symm

/-- 元の全 Kan 脚の台が通常の積錐なら、元の native 全錐は極限錐。 -/
lemma discreteSpaceCone_isLimit_of_readback_forgetLimit
    (h : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (discreteKanConeReadback F c K hc))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (discreteKanConeReadback F c K hc)).cast
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit (discreteKanConeReadback F c K hc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ h)).cast _
  exact (discreteKanConeReadback_eq F c K hc).symm ▸ hd

/-- 元の native 離散錐の極限性は、元の全 Kan 脚の豊穣 Hom 比較の同値性と同値。 -/
lemma discreteSpaceCone_isLimit_iff_readback_representableComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison (discreteKanConeReadback F c K hc) x) := by
  constructor
  · intro h
    have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (discreteKanConeReadback F c K hc)).cast
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)) :=
      discreteKanConeReadback_eq F c K hc ▸ h
    have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (discreteKanConeReadback F c K hc)) :=
      hd.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F).symm
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_discrete_representableComparison _).mp hs
  · intro h
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_discrete_representableComparison _).mpr h
    have hd := hs.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
    exact (discreteKanConeReadback_eq F c K hc).symm ▸ hd

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
