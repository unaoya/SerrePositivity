module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanApexConeTransportLeg
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeComparisonNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeConstantDiagramComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeConstantDiagramEdges

/-!
概要：頂点輸送の各脚の指定比較を、元の全錐円柱の上下三角形から構成する。
方針：指定三角形の比較の図式恒等成分だけを厳密に消去する。
規約：新たなホモトピーを選ばない。使われ方：元の指定 path と脚の二次の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {D : I ⥤ KanObject.{u}}
  (d : JoinCone (kanDiagramCoherentNerve D))
  {K L : KanObject.{u}} (a : K ⟶ L) {v : SpaceInfinity.{u} _⦋0⦌}
  (t : SpecifiedApexLimitConeTransport d (SSet.yonedaEquiv.symm v)
    (edgeApexPrism (coherentNerveEdge a)))
  (hv : v = coherentNerveVertex K) (hd : d.vertex = coherentNerveVertex L)

/-- 元の全錐円柱の上下三角形が与える、図式成分付きの指定脚比較。 -/
def kanApexConeTransportLegComparisonIso (i : I) :
    FunctorIso (kanApexConeTransportLeg d a t hv i ≫ kanConeDiagramComponent t.homotopy i)
      (a ≫ kanNativeConeLeg d L hd i) :=
  kanConeLegComparisonIso t.homotopy K L (kanApexConeTransport_vertex d a t hv) hd a
    (kanApexConeTransport_apexEdge d a t) i

/-- 図式の恒等成分を消した元の指定脚比較。 -/
def kanApexConeTransportLegIso (i : I) :
    FunctorIso (kanApexConeTransportLeg d a t hv i) (a ≫ kanNativeConeLeg d L hd i) :=
  functorIsoOfEq (kanApexConeTransportLegComparisonIso d a t hv hd i) (by
    rw [kanConeDiagramComponent_eq_id t.homotopy t.diagram]
    exact Category.comp_id _) rfl

/-- 端点の恒等成分の消去は元の指定脚比較の値を保持する。 -/
lemma kanApexConeTransportLegIso_heq (i : I) :
    HEq (kanApexConeTransportLegIso d a t hv hd i)
      (kanApexConeTransportLegComparisonIso d a t hv hd i) := functorIsoOfEq_heq _ _ _

/-- 輸送後の元の錐の各三角形からの指定合成比較。 -/
def kanApexConeTransportTriangleIso {i j : I} (m : i ⟶ j) :
    FunctorIso (kanApexConeTransportLeg d a t hv j)
      (kanApexConeTransportLeg d a t hv i ≫ D.map m) :=
  kanNativeConeTriangleIso t.cone K (kanApexConeTransport_vertex d a t hv) m

end SerrePositivity.InfinityCategories.F2
