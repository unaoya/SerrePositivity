module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：任意の dg 圏の閉同型を成分とする厳密自然変換は nerve の実関手同型を与える。
方針：頂点辺を閉射へ戻し、H⁰ 比較の同型反映と点ごとの可逆性判定を使う。
規約：始域・終域の Small 仮定は不要。実関手同型を構成する。
使われ方：異なる宇宙から持ち上げた加群値関手の全 Hom 自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {F G : DGFunctor R D E}

def dgStrictNatTransFunctorIsoOfClosedIso (η : StrictNatTrans F G)
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (G.obj x))
    (ha : ∀ x, η.app x = closedHomEquiv R E _ _ (a x).hom) :
    FunctorIso (dgNerve.map F) (dgNerve.map G) := by
  apply functorIsoOfPointwiseInvertibleHomotopy η.homotopy
  intro z
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  have he := dgStrictNatTrans_homotopy_vertex_edge η x
  rw [ha x] at he
  apply (isInvertibleEdge_congr he).mpr
  have hc : edgeClosed (edgeOfCycle (x := Simplex.vertex (F.obj x))
      (y := Simplex.vertex (G.obj x)) (closedHomEquiv R E _ _ (a x).hom)) =
      (a x).hom := (edgeClosedEquiv (Simplex.vertex (F.obj x))
        (Simplex.vertex (G.obj x))).apply_symm_apply _
  let e := edgeOfCycle (x := Simplex.vertex (F.obj x)) (y := Simplex.vertex (G.obj x))
    (closedHomEquiv R E _ _ (a x).hom)
  have hm : IsIso ((toH0 R E).map (SSet.Truncated.HomotopyCategory₂.homMk e)) := by
    rw [toH0_homMk, hc]
    infer_instance
  have hi : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (toH0 R E)
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk e)

end SerrePositivity.InfinityCategories
