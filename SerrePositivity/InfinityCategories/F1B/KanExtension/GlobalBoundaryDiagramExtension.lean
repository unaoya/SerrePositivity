module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalRelativeFiberAssembly
public import SerrePositivity.InfinityCategories.F1B.KanExtension.BoundaryRelativeCoconeExistence

/-!
概要：最初の境界頂点で局所的に普遍な相対 join 図式を標準単体全体へ延長する。
方針：各 fiber の境界余錐を転置して相対余錐を選び、指定された大域図式の上で組み立てる。
規約：欠けたパラメータは正次元の標準単体、元の図式を厳密に保つ。
使われ方：相対 join の普遍図式から元の図式への制限の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：境界上の相対 join 図式は、最初の頂点での局所余極限性から標準単体へ延長できる。
方針：各 fiber で境界固定の局所相対余錐を作り、coherent な族から大域図式へ戻す。
規約：元の全図式と境界上の全余錐を同時に固定する。
使われ方：普遍な Kan 図式への制限射の正次元の全境界充填。 -/
lemma exists_kanGlobalBoundary_diagram_extension {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p] (n : ℕ)
    (F : K ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ (ihom (boundary (n + 1) : SSet.{u})).obj D)
    (hFU : F ≫ (pre (boundary (n + 1)).ι).app D = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hfirst : ∀ c : C _⦋0⦌, IsColimitCone (kanCoconeFamilyAt
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (kanRelativeJoinFiberCocone p c H₀).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧ H ≫ (pre (boundary (n + 1)).ι).app D = H₀ ∧
        ∀ c : C _⦋0⦌, KanRelativeCoconeLifting ((pre (boundary (n + 1)).ι).app D)
          (kanRelativeJoinFiberCocone p c H) := by
  apply exists_kanGlobalRelative_diagram_with_relative_fibers p (boundary (n + 1)).ι F H₀ hFU
  intro c
  let a := SerrePositivity.InfinityCategories.F1B.functorTranspose (kanRelativeJoinFiberCocone p c H₀).val
  let d := SerrePositivity.InfinityCategories.F1B.functorTranspose (vertexFiberι p c ≫ F)
  have hw : joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫
      (kanRelativeJoinFiberCocone p c H₀).val =
        (vertexFiberι p c ≫ F) ≫ (pre (boundary (n + 1)).ι).app D := by
    rw [(kanRelativeJoinFiberCocone p c H₀).property, Category.assoc, ← hFU, ← Category.assoc]
  have ha : a ≫ coconeRestriction (vertexFiber p c) D = (boundary (n + 1)).ι ≫ d := by
    calc
      a ≫ coconeRestriction (vertexFiber p c) D =
          SerrePositivity.InfinityCategories.F1B.functorTranspose (joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫
            (kanRelativeJoinFiberCocone p c H₀).val) :=
        (SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left _ _).symm
      _ = SerrePositivity.InfinityCategories.F1B.functorTranspose ((vertexFiberι p c ≫ F) ≫
          (pre (boundary (n + 1)).ι).app D) := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hw
      _ = _ := SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right (boundary (n + 1)).ι (vertexFiberι p c ≫ F)
  obtain ⟨z, hz, hzu⟩ := exists_kanBoundaryRelativeCocone_of_first_colimit n a d ha (hfirst c)
  have hdiagram : joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫ z.val =
      vertexFiberι p c ≫ F := by
    exact z.property.trans (SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose (vertexFiberι p c ≫ F))
  refine ⟨⟨z.val, hdiagram⟩, hz, ?_⟩
  change z.val ≫ (pre (boundary (n + 1)).ι).app D = (kanRelativeJoinFiberCocone p c H₀).val
  simpa only [a, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose] using hzu

end SerrePositivity.InfinityCategories.F1B
