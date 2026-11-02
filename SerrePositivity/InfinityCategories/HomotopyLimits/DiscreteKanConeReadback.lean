module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeEdgeReconstruction
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableLimitEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanNativeConeLeg

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {J : Type u} (F : Discrete J ⥤ KanObject.{u})
  (c : JoinCone (kanDiagramCoherentNerve F))
  (K : KanObject.{u}) (hc : c.vertex = coherentNerveVertex K)

/-- 元の native 錐の全脚をそのまま戻した、元の Kan 対象を頂点とする通常の錐。 -/
def discreteKanConeReadback : Cone F where
  pt := K
  π := Discrete.natTrans (fun i ↦ F2.kanNativeConeLeg c K hc i)

/-- 元の native 全錐は、元の全 Kan 脚を持つ通常の錐の strict 表示そのもの。 -/
lemma discreteKanConeReadback_eq : c =
    (strictCoherentCone (discreteKanConeReadback F c K hc)).cast
      (strictCoherentDiagram_eq_kanDiagram F) := by
  apply discreteCone_ext_of_vertex_leg
  · rw [JoinCone.vertex_cast, strictCoherentCone_vertex]
    exact hc
  · intro j
    change (F2.nativeConeLeg c (ULift.up (ComposableArrows.mk₀ (Discrete.mk j)))).edge =
      (F2.nativeConeLeg (strictCoherentCone (discreteKanConeReadback F c K hc))
        (ULift.up (ComposableArrows.mk₀ (Discrete.mk j)))).edge
    rw [F2.nativeConeLeg_strict]
    exact (F2.kanNativeConeLeg_edge c K hc (Discrete.mk j)).symm

/-- 元の全 Kan 脚の台が通常の積錐なら、元の native 全錐は極限錐。 -/
lemma discreteSpaceCone_isLimit_of_readback_forgetLimit
    (h : IsLimit (kanObjectForget.mapCone (discreteKanConeReadback F c K hc))) :
    IsLimitCone c := by
  have hd : IsLimitCone ((strictCoherentCone (discreteKanConeReadback F c K hc)).cast
      (strictCoherentDiagram_eq_kanDiagram F)) :=
    (strictCoherentCone_isLimit_of_discrete_homLimit (discreteKanConeReadback F c K hc)
      (kanObjectHomCone_isLimit_of_forget _ h)).cast _
  exact (discreteKanConeReadback_eq F c K hc).symm ▸ hd

/-- 元の native 離散錐の極限性は、元の全 Kan 脚の豊穣 Hom 比較の同値性と同値。 -/
lemma discreteSpaceCone_isLimit_iff_readback_representableComparison :
    IsLimitCone c ↔ ∀ x : KanObject.{u}, IsSimplicialHomotopyEquivalence
      (representableHomotopyLimitComparison (discreteKanConeReadback F c K hc) x) := by
  constructor
  · intro h
    have hd : IsLimitCone ((strictCoherentCone (discreteKanConeReadback F c K hc)).cast
        (strictCoherentDiagram_eq_kanDiagram F)) :=
      discreteKanConeReadback_eq F c K hc ▸ h
    have hs : IsLimitCone (strictCoherentCone (discreteKanConeReadback F c K hc)) :=
      hd.cast (strictCoherentDiagram_eq_kanDiagram F).symm
    exact (strictCoherentCone_isLimit_iff_discrete_representableComparison _).mp hs
  · intro h
    have hs := (strictCoherentCone_isLimit_iff_discrete_representableComparison _).mpr h
    have hd := hs.cast (strictCoherentDiagram_eq_kanDiagram F)
    exact (discreteKanConeReadback_eq F c K hc).symm ▸ hd

end SerrePositivity.InfinityCategories.HomotopyLimits
