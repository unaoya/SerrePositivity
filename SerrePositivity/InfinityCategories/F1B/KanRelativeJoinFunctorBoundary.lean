module

public import SerrePositivity.InfinityCategories.F1B.KanGlobalBoundaryDiagramExtension
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFiberTranspose
public import SerrePositivity.InfinityCategories.Stable.PastingRightCocone

/-!
概要：相対 join 上の関手の制限の正次元の境界充填。
方針：境界の関手を転置し、最初の頂点の fiber の余極限性から大域図式を延長して戻す。
規約：境界の他の頂点に普遍性は要求しない。
使われ方：普遍な相対 join 図式から元の図式への制限の写像空間の制御。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：最初の境界図式が各 fiber で普遍なら、相対 join 上の関手の境界を全体へ延長できる。
方針：局所の余錐の族の境界充填と大域的な相対組み立てを転置で関手の族へ戻す。
規約：境界と元の図式を厳密に固定する。
使われ方：普遍図式の制限射の始点境界充填を証明する。 -/
lemma exists_kanRelativeJoin_functor_boundary_extension {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p] (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (relativeJoin p (𝟙 C))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj D)
    (ha : a ≫ (pre (relativeJoinInl p (𝟙 C))).app D = (boundary (n + 1)).ι ≫ d)
    (hfirst : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c
      ((functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm
        (a.app (Opposite.op ⦋0⦌)
          ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)))) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (relativeJoin p (𝟙 C))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧ f ≫ (pre (relativeJoinInl p (𝟙 C))).app D = d := by
  have hFU : kanFunctorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      relativeJoinInl p (𝟙 C) ≫ kanFunctorTranspose a := by
    have h := congrArg kanFunctorTranspose ha
    rw [kanFunctorTranspose_pre_right, kanFunctorTranspose_pre_left] at h
    exact h.symm
  have hlocal : ∀ c : C _⦋0⦌, IsColimitCone (kanCoconeFamilyAt
      (kanFunctorTranspose (kanRelativeJoinFiberCocone p c (kanFunctorTranspose a)).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩) := by
    intro c
    exact (isColimitCone_iff_of_val_eq _ _
      (kanRelativeJoinFiberCocone_transpose_familyAt_val p c a _)).2 (hfirst c)
  obtain ⟨H, hHF, hHA, _⟩ := exists_kanGlobalBoundary_diagram_extension p n
    (kanFunctorTranspose d) (kanFunctorTranspose a) hFU hlocal
  refine ⟨kanFunctorTranspose H, ?_, ?_⟩
  · rw [← kanFunctorTranspose_pre_right, hHA, kanFunctorTranspose_transpose]
  · rw [← kanFunctorTranspose_pre_left, hHF, kanFunctorTranspose_transpose]

end SerrePositivity.InfinityCategories.F1B
