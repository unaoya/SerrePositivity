module

public import SerrePositivity.EInfinity.Modules.DGGraphCounit
public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCounitHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.IntervalEndpointTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitMappingAdjunction

/-!
# 生の dg nerve 上での graph 延長・制限随伴

概要：HA §4.2.3 の同じ graph 延長と制限を、全関手圏の随伴にする。
方針：指定余単位の全次数普遍性と、同じ厳密 dg 自然変換の全ホモトピーを使う。
規約：H⁰ 上の随伴だけを native な随伴とは見なさない。
使われ方：加群の局所化後の同じ restriction の右随伴比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open scoped Simplicial
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 概要：同じ graph 余単位の実ホモトピー（HA §4.2.3）。
方針：既存の全 Hom 自然性を dg nerve へ送る。
規約：同じ二つの生の実関手。使われ方：native な随伴の余単位。 -/
def graphCounitHomotopy (F : DGFunctor A D E) :
    SSet.Homotopy (N (dgModuleRestriction A D E F.op) ≫ N (dgModuleExtension A D E F))
      (𝟙 (dgModuleNerve A E)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] using
      (dgExtensionCounitStrict A D E F).homotopy

/-- 概要：実ホモトピーの頂点辺は元の指定余単位（HA §4.2.3）。
方針：厳密 dg 自然変換の実成分公式を使う。
規約：ホモトピーの端点だけでなく同じ辺を保持。使われ方：写像空間の標準比較。 -/
lemma graphCounitHomotopy_vertex_edge (F : DGFunctor A D E) (M : RightModule A E) :
    (simplicialHomotopyVertexEdge (graphCounitHomotopy A D E F) (Simplex.vertex M)).edge =
      (dgClosedEdge A (RightModule A E) (functorExtensionCounit A D E F M)).edge := by
  change (simplicialHomotopyVertexEdge (dgExtensionCounitStrict A D E F).homotopy
    (Simplex.vertex M)).edge = _
  exact dgStrictNatTrans_homotopy_vertex_edge (dgExtensionCounitStrict A D E F) M

/-- 概要：同じ生の dg 延長・制限の native 随伴（HA §4.2.3）。
方針：同じ余単位による全区間写像空間の同値から両三角式を得る。
規約：全関手圏の随伴。使われ方：解像度付き restriction の随伴。 -/
def graphRawAdjunction (F : DGFunctor A D E) :
    QCatAdjunction (N (dgModuleExtension A D E F)) (N (dgModuleRestriction A D E F.op)) := by
  apply qcatAdjunctionOfCounitIntervalCondition (graphCounitHomotopy A D E F)
  intro x y
  obtain ⟨P, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := RightModule A D)).symm.surjective x
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := RightModule A E)).symm.surjective y
  let e := graphUniversalCounit A D E F M
  exact intervalFunctorPostcompose_equivalence_of_endpoint
    (N (dgModuleExtension A D E F)) (Simplex.vertex P)
    ((N (dgModuleRestriction A D E F.op)).app _ (Simplex.vertex M)) (Simplex.vertex e.source)
    (simplicialHomotopyVertexEdge (graphCounitHomotopy A D E F) (Simplex.vertex M))
    (SSet.Edge.ofTruncated (dgClosedEdge A (RightModule A E) e.counit))
    (dgFunctorNerve_vertex (dgModuleRestriction A D E F.op) M)
    (dgFunctorNerve_vertex (dgModuleExtension A D E F) P)
    (dgFunctorNerve_vertex (dgModuleExtension A D E F) e.source) rfl
    (graphCounitHomotopy_vertex_edge A D E F M)
    (e.nativeIntervalMap_isSimplicialHomotopyEquivalence P)

end SerrePositivity.EInfinity.Modules
