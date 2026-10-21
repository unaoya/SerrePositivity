module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiscreteLegHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteKanConeReadback
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductNative

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の頂点を共有する native 離散全錐の極限性は、元の全 Kan 脚のホモトピーで不変。 -/
lemma discreteSpaceCone_isLimit_iff_of_leg_homotopies {J : Type u}
    (F : Discrete J ⥤ KanObject.{u}) (c d : JoinCone (kanDiagramCoherentNerve F))
    (K : KanObject.{u}) (hc : c.vertex = coherentNerveVertex K)
    (hd : d.vertex = coherentNerveVertex K)
    (H : ∀ i, SSet.Homotopy (F2.kanNativeConeLeg c K hc i) (F2.kanNativeConeLeg d K hd i)) :
    IsLimitCone c ↔ IsLimitCone d := by
  have he := kanDiscreteCone_isLimit_iff_of_leg_homotopies F K H
  have ec := discreteKanConeReadback_eq F c K hc
  have ed := discreteKanConeReadback_eq F d K hd
  constructor
  · intro h
    have hcs := (ec ▸ h).cast (strictCoherentDiagram_eq_kanDiagram F).symm
    have hds := he.mp hcs
    exact ed.symm ▸ hds.cast (strictCoherentDiagram_eq_kanDiagram F)
  · intro h
    have hds := (ed ▸ h).cast (strictCoherentDiagram_eq_kanDiagram F).symm
    have hcs := he.mpr hds
    exact ec.symm ▸ hcs.cast (strictCoherentDiagram_eq_kanDiagram F)

/-- 元の有限錐の全脚が元の反復積の射影にホモトピックなら、元の全錐は極限錐。 -/
lemma finiteSpaceCone_isLimit_of_projection_homotopies (n : ℕ)
    (E : Fin (n + 1) → KanObject.{u})
    (c : JoinCone (kanDiagramCoherentNerve (finiteKanProductDiagram n E)))
    (hc : c.vertex = coherentNerveVertex (finiteKanProductObject n E))
    (H : ∀ i, Nonempty (SSet.Homotopy
      (F2.kanNativeConeLeg c (finiteKanProductObject n E) hc i)
      (nonemptyFiniteSSetProjection n (fun j ↦ (E j).obj) i.as.down))) : IsLimitCone c := by
  apply (discreteSpaceCone_isLimit_iff_of_leg_homotopies (finiteKanProductDiagram n E) c
    (finiteKanProductNativeCone n E) (finiteKanProductObject n E) hc
    (finiteKanProductNativeCone_vertex n E) (fun i ↦ ?_)).mpr
      (finiteKanProductNativeCone_isLimit n E)
  rw [finiteKanProductNativeCone_kanLeg]
  exact Classical.choice (H i)

end SerrePositivity.InfinityCategories.HomotopyLimits
