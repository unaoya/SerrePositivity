module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeCancellation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteVerdierDenominators

/-! # 商で一致する有限族の実分母による同時均等化

概要：商で一致する有限個の元の二辺を、一つの元の実分母で同時に均等化する。
方針：各対の相対零化の分母を共通化し、共有合成辺への実二単体を回収する。
規約：入力辺は厳密に保持する。使われ方：局所化の有限比較の相対条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商で一致する有限族は、一つの実分母と各対の共有合成辺への実二単体で均等化できる。 -/
theorem dgQuotientEdges_exists_cancelingTriangles (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {n : ℕ} {x : D} {y : Fin n → D}
    (f g : ∀ i, Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (y i)))
    (h : ∀ i, Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) (f i)) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) (g i))) :
    ∃ (q : D) (t : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), t.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ k : ∀ i, Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (y i)),
        ∀ i, Nonempty (Truncated.Edge.CompStruct t (f i) (k i)) ∧
          Nonempty (Truncated.Edge.CompStruct t (g i) (k i)) := by
  choose q s hs k hf hg using fun i =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientEdge_exists_cancelingTriangles A D P hP (f i) (g i) (h i)
  obtain ⟨q', t, ht, r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_commonDenominator A D P q s hs
  have he (i : Fin n) : Truncated.HomotopyCategory.homMk t ≫
      Truncated.HomotopyCategory.homMk (f i) =
      Truncated.HomotopyCategory.homMk t ≫ Truncated.HomotopyCategory.homMk (g i) := by
    have hs' := Truncated.HomotopyCategory.homMk_comp_homMk (hr i).2.some
    have hf' := Truncated.HomotopyCategory.homMk_comp_homMk (hf i).some
    have hg' := Truncated.HomotopyCategory.homMk_comp_homMk (hg i).some
    rw [← hs', Category.assoc, hf', ← hg', ← Category.assoc, hs']
  choose k' hk' using fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q') (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (y i))
    (Truncated.HomotopyCategory.homMk (V := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) t ≫
      Truncated.HomotopyCategory.homMk (f i))
  refine ⟨q', t, ht, k', fun i => ?_⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (hk' i).symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ((he i).symm.trans (hk' i).symm)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
