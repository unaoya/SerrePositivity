module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiscreteLegHomotopy
public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanNativeConeLeg

/-!
概要：元の Kan 対象と元の離散全脚から、同じ全一単体を持つ native 全錐を構成する。
方針：同じ通常の離散錐の coherent 表示を使い、読み戻した全 Kan 脚を厳密に回収する。
規約：脚の極限性や同値性を仮定しない。
使われ方：元の評価全脚の Kan 像を変更せずに有限積の極限性を判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {J : Type u} (F : Discrete J ⥤ KanObject.{u}) (K : KanObject.{u})
  (f : (i : Discrete J) → K ⟶ F.obj i)

/-- 元の離散図式・頂点・全 Kan 脚を保持する native 全錐。 -/
def kanDiscreteNativeConeOfLegs : JoinCone (kanDiagramCoherentNerve F) :=
  (strictCoherentCone (kanDiscreteConeOfLegs F K f)).cast (strictCoherentDiagram_eq_kanDiagram F)

/-- 元の全錐の頂点は、指定された同じ Kan 対象の頂点。 -/
lemma kanDiscreteNativeConeOfLegs_vertex :
    (kanDiscreteNativeConeOfLegs F K f).vertex = coherentNerveVertex K :=
  strictCoherentCone_vertex (kanDiscreteConeOfLegs F K f)

/-- 元の全錐の脚を Kan 射へ戻すと、指定した元の脚そのもの。 -/
lemma kanDiscreteNativeConeOfLegs_kanLeg (i : Discrete J) :
    F2.kanNativeConeLeg (kanDiscreteNativeConeOfLegs F K f) K
      (kanDiscreteNativeConeOfLegs_vertex F K f) i = f i := by
  have h : F2.kanNativeConeLegEdge (kanDiscreteNativeConeOfLegs F K f) K
      (kanDiscreteNativeConeOfLegs_vertex F K f) i = coherentNerveEdge (f i) := by
    apply SSet.Edge.ext
    exact F2.nativeConeLeg_strict (kanDiscreteConeOfLegs F K f) i
  exact (congrArg coherentNerveEdgeToHom h).trans (coherentNerveEdgeToHom_edge _)

end SerrePositivity.InfinityCategories.HomotopyLimits
