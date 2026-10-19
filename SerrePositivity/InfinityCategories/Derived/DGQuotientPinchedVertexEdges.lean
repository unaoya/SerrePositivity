module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedTopComparisons
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearBoundaryEdgeEndpoints

/-! # 指定商頂点の有限族の共通分母後の実 pinched 辺

概要：任意の有限個の指定商頂点を、一つの元の分母後で元の頂点の像へ実辺で結ぶ。
方針：零次元には指定すべき真部分集合がなく、最上位比較を実辺へ昇格できる。
規約：全入力商頂点を固定する。使われ方：相対局所化比較の零次元の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 指定された商頂点を、共通実分母の後で元の頂点の像へ実辺で結ぶ。 -/
theorem dgQuotientFinite_exists_pinchedVertexEdges (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D)
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ t : ∀ i, LinearSimplex A q (y i) 0,
        ∀ i, Nonempty ((DGNerve.pinchedHom A (QuotientObject D P)
          ((inclusion A D P).obj q) ((inclusion A D P).obj (y i))).Edge
          (pinchedLinearSimplexMap (dgClosedPrecomposition A (QuotientObject D P)
            (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
            (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s)) (g i)).toPinched
          (pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i)).toPinched) := by
  have hfull (J : Finset (Fin (0 + 1))) (hJ : J.Nonempty) : J = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun j => by
      obtain ⟨a, ha⟩ := hJ
      have haj : a = j := by omega
      simpa only [haj] using ha)
  obtain ⟨q, s, hs, t, _, hc⟩ := dgQuotientFinite_exists_pinchedTopComparisons A D P hP
    x y (fun _ => 0) (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim) g
    (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
  refine ⟨q, s, hs, t, ?_⟩
  intro i
  obtain ⟨c⟩ := hc i
  exact ⟨c.edge_zero⟩

end SerrePositivity.InfinityCategories
