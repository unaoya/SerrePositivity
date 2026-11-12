module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientClosedCancellation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedMappedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges

/-! # 商で一致する実二辺の元の実分母による均等化

概要：商の通常の h で一致する元の実二辺は、一つの元の実分母で均等化できる。
方針：閉射の相対零化を実辺へ戻し、共有合成辺を持つ二つの実合成二単体を構成する。
規約：元の二辺を厳密に保持。使われ方：分数表示の相対比較と有限族の同時化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商で一致する元の二辺は、実分母と共有合成辺への二つの実二単体で均等化できる。 -/
theorem dgQuotientEdge_exists_cancelingTriangles (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {x y : D}
    (f g : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
    (h : Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) f) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) g)) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y),
        Nonempty (Truncated.Edge.CompStruct s f k) ∧
          Nonempty (Truncated.Edge.CompStruct s g k) := by
  have hQ := congrArg
    (fun a => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (QuotientObject D P)).functor.map a) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge_closed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge_closed] at hQ
  obtain ⟨q, s, hs, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosed_exists_cancelingDenominator A D P hP
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed g) hQ
  have hc : Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s) ≫
      Truncated.HomotopyCategory.homMk f =
      Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s) ≫
        Truncated.HomotopyCategory.homMk g := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A D).functor.map_injective
    simpa only [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] using he
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
    (Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s) ≫
      Truncated.HomotopyCategory.homMk f)
  exact ⟨q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s, hs, k,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) hk.symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (hc.symm.trans hk.symm)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
