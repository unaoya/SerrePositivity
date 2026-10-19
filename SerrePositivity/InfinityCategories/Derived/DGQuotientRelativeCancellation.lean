module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedCancellation
public import SerrePositivity.InfinityCategories.Derived.DGClosedMappedEdges
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEdges

/-! # 商で一致する実二辺の元の実分母による均等化

概要：商の通常の h で一致する元の実二辺は、一つの元の実分母で均等化できる。
方針：閉射の相対零化を実辺へ戻し、共有合成辺を持つ二つの実合成二単体を構成する。
規約：元の二辺を厳密に保持。使われ方：分数表示の相対比較と有限族の同時化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商で一致する元の二辺は、実分母と共有合成辺への二つの実二単体で均等化できる。 -/
theorem dgQuotientEdge_exists_cancelingTriangles (P : Set D) (hP : localKFlat A D P)
    {x y : D}
    (f g : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex x) (Simplex.vertex y))
    (h : Truncated.HomotopyCategory.homMk
        (dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) f) =
      Truncated.HomotopyCategory.homMk
        (dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) g)) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
      ∃ k : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
        (Simplex.vertex q) (Simplex.vertex y),
        Nonempty (Truncated.Edge.CompStruct s f k) ∧
          Nonempty (Truncated.Edge.CompStruct s g k) := by
  have hQ := congrArg
    (fun a => (dgStableHomotopyEquivalence A (QuotientObject D P)).functor.map a) h
  rw [dgStableHomotopyEquivalence_map_homMk, dgStableHomotopyEquivalence_map_homMk,
    dgClosedMappedEdge_closed, dgClosedMappedEdge_closed] at hQ
  obtain ⟨q, s, hs, he⟩ := dgQuotientClosed_exists_cancelingDenominator A D P hP
    (edgeClosed f) (edgeClosed g) hQ
  have hc : Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (dgNerve A D))
      (dgClosedEdge A D s) ≫
      Truncated.HomotopyCategory.homMk f =
      Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (dgNerve A D))
      (dgClosedEdge A D s) ≫
        Truncated.HomotopyCategory.homMk g := by
    apply (dgStableHomotopyEquivalence A D).functor.map_injective
    simpa only [Functor.map_comp, dgStableHomotopyEquivalence_map_homMk,
      dgClosedEdge_closed] using he
  obtain ⟨k, hk⟩ := homotopyCategory_homMk_surjective (Simplex.vertex q) (Simplex.vertex y)
    (Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (dgNerve A D))
      (dgClosedEdge A D s) ≫
      Truncated.HomotopyCategory.homMk f)
  exact ⟨q, dgClosedEdge A D s, hs, k,
    compStruct_nonempty_of_homMk_fac (X := dgNerve A D) hk.symm,
    compStruct_nonempty_of_homMk_fac (X := dgNerve A D) (hc.symm.trans hk.symm)⟩

end SerrePositivity.InfinityCategories
