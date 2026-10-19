module
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTrans
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-! # 全 Hom 自然な加群同型族による実関手同型

概要：全次数で自然な閉加群同型族は native dg nerve の関手同型を与える。
方針：実ホモトピーの頂点辺を指定 cycle の辺と同定し、同型性を反映する。
規約：単体的ホモトピー自体を使う。使われ方：延長と Yoneda の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (E : Type v) [DGCategory A E] [Small.{u} E]
variable {D : Type (max (u + 1) v)} [DGCategory A D]
variable {F G : DGFunctor A D (RightModule A E)}
variable (η : StrictNatTrans F G)
variable (a : ∀ x, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
  ForgetEnrichment.of (Complex A) (G.obj x))
variable (hc : ∀ x, η.app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a x)))
include hc

/-- 指定した実同型の cycle を成分に持つホモトピーは全実頂点で可逆。 -/
lemma dgModuleStrictNatTrans_pointwise (ha : ∀ x, IsIso (a x))
    (z : (dgNerve A D) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge η.homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  have he := dgStrictNatTrans_homotopy_vertex_edge η x
  rw [hc x] at he
  apply (isInvertibleEdge_congr he).mpr
  have := dgModuleEdge_isIso_of_homotopy A E (a x) (by
    let := ha x
    infer_instance)
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A E (a x)).toTruncated)

/-- 実加群同型を成分に持つ厳密自然変換を実関手圏の同型へ束ねる。 -/
def dgModuleFunctorIsoOfStrictNatTrans (ha : ∀ x, IsIso (a x)) :
    FunctorIso (dgNerve.map F) (dgNerve.map G) :=
  functorIsoOfPointwiseInvertibleHomotopy η.homotopy
    (dgModuleStrictNatTrans_pointwise A E η a hc ha)

end SerrePositivity.InfinityCategories
