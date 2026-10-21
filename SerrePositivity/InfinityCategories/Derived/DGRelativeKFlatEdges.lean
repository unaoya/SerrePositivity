module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatResolutionLocalization
/-!
概要：K-flat 全部分圏の準同型辺から、元の両 K-flat 加群間の実閉準同型を回収する。
方針：辺条件の同じ閉射表示と、両端頂点の実 K-flat 条件を照合する。
規約：辺や両端を選び直さない。使われ方：任意 kernel による準同型保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
/-- K-flat 準同型辺を表す元の閉射の始点も、同じ実加群の K-flat 条件を持つ。 -/
lemma dgRelativeKFlatEdge_source_relativeKFlat
    (s : (dgRelativeKFlatModuleNerve R E) _⦋1⦌)
    {M N : ClosedCategory R (RightModule R E)} (f : M ⟶ N)
    (he : (dgClosedEdge R (RightModule R E) f).edge = s.val) :
    moduleRelativeKFlat R E (ForgetEnrichment.to (Complex R) M) := by
  have hx := fullSubcomplexOnVertices_vertex ((dgRelativeKFlatModuleNerve R E).δ 1 s)
  change moduleRelativeKFlat R E
    (Simplex.vertexEquiv ((dgModuleNerve R E).δ 1 s.val)) at hx
  have hm := congrArg (fun t => Simplex.vertexEquiv ((dgModuleNerve R E).δ 1 t)) he
  change ForgetEnrichment.to (Complex R) M =
    Simplex.vertexEquiv ((dgModuleNerve R E).δ 1 s.val) at hm
  exact hm.symm ▸ hx
/-- K-flat 準同型辺を表す元の閉射の終点も、同じ実加群の K-flat 条件を持つ。 -/
lemma dgRelativeKFlatEdge_target_relativeKFlat
    (s : (dgRelativeKFlatModuleNerve R E) _⦋1⦌)
    {M N : ClosedCategory R (RightModule R E)} (f : M ⟶ N)
    (he : (dgClosedEdge R (RightModule R E) f).edge = s.val) :
    moduleRelativeKFlat R E (ForgetEnrichment.to (Complex R) N) := by
  have hx := fullSubcomplexOnVertices_vertex ((dgRelativeKFlatModuleNerve R E).δ 0 s)
  change moduleRelativeKFlat R E
    (Simplex.vertexEquiv ((dgModuleNerve R E).δ 0 s.val)) at hx
  have hm := congrArg (fun t => Simplex.vertexEquiv ((dgModuleNerve R E).δ 0 t)) he
  change ForgetEnrichment.to (Complex R) N =
    Simplex.vertexEquiv ((dgModuleNerve R E).δ 0 s.val) at hm
  exact hm.symm ▸ hx
/-- K-flat 加群間の実閉準同型辺を反転すれば、同じ全部分圏の全準同型辺を反転する。 -/
lemma dgRelativeKFlatQuasiIsomorphismEdges_inverts {Y : SSet.{max (u + 1) v}}
    (q : dgModuleNerve R E ⟶ Y)
    (h : ∀ (M N : ClosedCategory R (RightModule R E)),
      moduleRelativeKFlat R E (ForgetEnrichment.to (Complex R) M) →
      moduleRelativeKFlat R E (ForgetEnrichment.to (Complex R) N) →
      ∀ f : M ⟶ N, moduleQuasiIso R E f → IsInvertibleEdge
        ((dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q))) :
    InvertsEdges (dgRelativeKFlatModuleInclusion R E ≫ q)
      (dgRelativeKFlatQuasiIsomorphismEdges R E) := by
  intro s hs
  obtain ⟨M, N, f, hf, he⟩ := hs
  have hi := h M N (dgRelativeKFlatEdge_source_relativeKFlat R E s f he)
    (dgRelativeKFlatEdge_target_relativeKFlat R E s f he) f hf
  exact (isInvertibleEdge_congr (X := Y)
    (e := (edgeOfSimplex s).map
      ((truncation 2).map (dgRelativeKFlatModuleInclusion R E ≫ q)))
    (f := (dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q))
    (congrArg (fun t => q.app (Opposite.op ⦋1⦌) t) he.symm)).mpr hi
end SerrePositivity.InfinityCategories
