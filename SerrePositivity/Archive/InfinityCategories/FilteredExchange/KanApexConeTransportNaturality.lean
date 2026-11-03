module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanApexConeTransportIsos
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoConstantSquare

/-!
概要：頂点輸送の元の指定脚比較は、両錐の指定三角形に対して整合する。
方針：三つの四面体の自然性で図式の恒等成分と定値な指定二単体を消去する。
規約：元の指定値の等式。使われ方：coherent 余極限後の二脚と指定 path の整合。
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

/-- 同じ全錐円柱からの脚比較は元の両錐の指定三角形の値と整合する。 -/
lemma kanApexConeTransportLegIso_naturality {i j : I} (m : i ⟶ j) :
    kanApexConeTransportTriangleIso d a t hv m ≪≫
      (kanApexConeTransportLegIso d a t hv hd i).postcomp (D.map m) =
    kanApexConeTransportLegIso d a t hv hd j ≪≫
      (kanNativeConeTriangleIso d L hd m).precomp (show K.obj ⟶ L.obj from a) := by
  exact functorIso_constant_square (D.map m)
    (kanConeDiagramComponent t.homotopy i) (kanConeDiagramComponent t.homotopy j)
    (kanApexConeTransportTriangleIso d a t hv m) _
    (kanApexConeTransportLegComparisonIso d a t hv hd i)
    (kanApexConeTransportLegComparisonIso d a t hv hd j)
    (kanConeDiagramComparisonIso t.homotopy m)
    (kanApexConeTransportLegIso d a t hv hd i) (kanApexConeTransportLegIso d a t hv hd j)
    (kanConeDiagramComponent_eq_id t.homotopy t.diagram i)
    (kanConeDiagramComponent_eq_id t.homotopy t.diagram j)
    (kanConeDiagramComparisonIso_isFunctorEqIso t.homotopy t.diagram m)
    (kanApexConeTransportLegIso_heq d a t hv hd i) (kanApexConeTransportLegIso_heq d a t hv hd j)
    (kanConeLegComparisonIso_naturality t.homotopy K L
      (kanApexConeTransport_vertex d a t hv) hd a (kanApexConeTransport_apexEdge d a t) m)

end SerrePositivity.InfinityCategories.F2
