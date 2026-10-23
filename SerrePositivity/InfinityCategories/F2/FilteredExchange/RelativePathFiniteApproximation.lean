module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathBoundaryDiagram
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.MonicAnchoredFiniteApproximation

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定相対 path は、全境界を単射に保つ有限模型で近似できる。
方針：相対境界の元の図式を anchor とする既存の有限近似を使う。
規約：全相対境界上の比較円柱が厳密に定値。使われ方：元の境界付きの有限輸送。 -/
lemma continuousKanReplacement_relative_path_finite_approximation {K E : SSet.{u}} [K.Finite]
    (A : K.Subcomplex) (f g : K ⟶ E) (a : (Δ[1] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ E)
    (h₀ : prismEndpoint 0 (A : SSet.{u}) ≫ a = A.ι ≫ f)
    (h₁ : prismEndpoint 1 (A : SSet.{u}) ≫ a = A.ι ≫ g)
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj E)
    (hr₀ : prismEndpoint 0 K ≫ r = f ≫ continuousKanReplacementUnit.app E)
    (hr₁ : prismEndpoint 1 K ≫ r = g ≫ continuousKanReplacementUnit.app E)
    (hra : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ r = a ≫ continuousKanReplacementUnit.app E) :
    ∃ M : SSet.{u}, ∃ m : relativePathBoundaryShape A ⟶ M, ∃ q : M ⟶ E,
      ∃ z : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj M,
        M.Finite ∧ Mono m ∧ m ≫ q = relativePathBoundaryDiagram A f g a h₀ h₁ ∧
        relativePathBoundaryι A ≫ z = m ≫ continuousKanReplacementUnit.app M ∧
        ∃ G : SSet.Homotopy r (z ≫ continuousKanReplacement.map q),
          (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ G.h =
            fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
              relativePathBoundaryDiagram A f g a h₀ h₁ ≫ continuousKanReplacementUnit.app E := by
  have hd : relativePathBoundaryDiagram A f g a h₀ h₁ ≫ continuousKanReplacementUnit.app E =
      relativePathBoundaryι A ≫ r := by
    apply (Subcomplex.unionProd.isPushout (boundary 1) A).hom_ext
    · change relativePathBoundarySide A ≫
        (relativePathBoundaryDiagram A f g a h₀ h₁ ≫ continuousKanReplacementUnit.app E) =
          relativePathBoundarySide A ≫ (relativePathBoundaryι A ≫ r)
      rw [← Category.assoc, relativePathBoundaryDiagram_side, ← Category.assoc,
        relativePathBoundarySide_ι]
      exact hra.symm
    · change relativePathBoundaryEnds A ≫
        (relativePathBoundaryDiagram A f g a h₀ h₁ ≫ continuousKanReplacementUnit.app E) =
          relativePathBoundaryEnds A ≫ (relativePathBoundaryι A ≫ r)
      rw [← Category.assoc, relativePathBoundaryDiagram_ends, ← Category.assoc,
        relativePathBoundaryEnds_ι, intervalBoundaryDiagram_postcomp,
        intervalBoundaryDiagram_restrict, hr₀, hr₁]
  exact continuousKanReplacement_monic_anchored_finite_approximation (relativePathBoundaryι A)
    (relativePathBoundaryDiagram A f g a h₀ h₁) r hd

end SerrePositivity.InfinityCategories.F2
