module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalBoundaryPostcomposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.MonicAnchoredFiniteApproximation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryDiagram

/-!
概要：両端と指定部分 path を同時に固定した、指定 Kan path の有限模型近似。
方針：元の全相対境界を有限な単射として貼り、境界固定の有限近似を適用する。
規約：比較円柱は両端上と部分 path 全体の上で全時刻定値。
使われ方：一般 coherent filtered 引き戻しの境界付き標的検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：指定相対 path は、全境界を単射に保つ有限模型で近似できる。
方針：相対境界の元の図式を anchor とする既存の有限近似を使う。
規約：全相対境界上の比較円柱が厳密に定値。使われ方：元の境界付きの有限輸送。 -/
lemma continuousKanReplacement_relative_path_finite_approximation {K E : SSet.{u}} [K.Finite]
    (A : K.Subcomplex) (f g : K ⟶ E) (a : (Δ[1] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A : SSet.{u}) ≫ a = A.ι ≫ f)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A : SSet.{u}) ≫ a = A.ι ≫ g)
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
    (hr₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ r = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
    (hr₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ r = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
    (hra : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ r = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) :
    ∃ M : SSet.{u}, ∃ m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M, ∃ q : M ⟶ E,
      ∃ z : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M,
        M.Finite ∧ Mono m ∧ m ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁ ∧
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M ∧
        ∃ G : SSet.Homotopy r (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map q),
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ G.h =
            fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
              _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E := by
  have hd : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r := by
    apply (Subcomplex.unionProd.isPushout (boundary 1) A).hom_ext
    · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) =
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r)
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_side, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide_ι]
      exact hra.symm
    · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) =
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r)
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_ends, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_postcomp,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, hr₀, hr₁]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_monic_anchored_finite_approximation (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A f g a h₀ h₁) r hd

end SerrePositivity.InfinityCategories.Project.FilteredExchange
