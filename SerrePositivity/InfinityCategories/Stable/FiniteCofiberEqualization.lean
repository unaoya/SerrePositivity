module
public import SerrePositivity.InfinityCategories.Stable.FiniteHoEqualization
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-! # 実辺の有限同時均等化

概要：分母の後で一致する有限族を、一つの実分母と共有合成辺への実二単体で均等化する。
方針：h C の同時均等化を実辺に持ち上げ、二つの合成を同じ辺で表示する。
規約：全ての入力辺を保持。使われ方：coherent 分数表示の有限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X] [IsStable X]

/-- 有限個の等式を一つの実分母と、共有合成辺を持つ実二単体で同時に実現する。 -/
theorem cofiberStableEdges_equalizeFinite (P : Set (X _⦋0⦌))
    {n : ℕ} {x : X _⦋0⦌} {y z : Fin n → X _⦋0⦌}
    (f g : ∀ i, Truncated.Edge (X := (truncation 2).obj X) x (y i))
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj X) (y i) (z i))
    (hs : ∀ i, (s i).edge ∈ cofiberLocalizingEdges {a | StableVertexClosure P a})
    (h : ∀ i, SSet.Truncated.HomotopyCategory.homMk (f i) ≫
      SSet.Truncated.HomotopyCategory.homMk (s i) =
      SSet.Truncated.HomotopyCategory.homMk (g i) ≫
        SSet.Truncated.HomotopyCategory.homMk (s i)) :
    ∃ (q : X _⦋0⦌) (t : Truncated.Edge (X := (truncation 2).obj X) q x),
      t.edge ∈ cofiberLocalizingEdges {a | StableVertexClosure P a} ∧
      ∃ k : ∀ i, Truncated.Edge (X := (truncation 2).obj X) q (y i),
        ∀ i, Nonempty (Truncated.Edge.CompStruct t (f i) (k i)) ∧
          Nonempty (Truncated.Edge.CompStruct t (g i) (k i)) := by
  obtain ⟨q, t, ht, he⟩ := stableHoClosure_equalizeFinite P
    (fun i => SSet.Truncated.HomotopyCategory.homMk (f i))
    (fun i => SSet.Truncated.HomotopyCategory.homMk (g i))
    (fun i => SSet.Truncated.HomotopyCategory.homMk (s i))
    (fun i => (cofiberStableEdges_iff_trW P (s i)).mp (hs i)) h
  obtain ⟨q, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective q
  obtain ⟨t, rfl⟩ := homotopyCategory_homMk_surjective q x t
  choose k hk using fun i => homotopyCategory_homMk_surjective q (y i)
    (SSet.Truncated.HomotopyCategory.homMk t ≫
      SSet.Truncated.HomotopyCategory.homMk (f i))
  refine ⟨q, t, (cofiberStableEdges_iff_trW P t).mpr ht, k, fun i => ?_⟩
  exact ⟨compStruct_nonempty_of_homMk_fac (hk i).symm,
    compStruct_nonempty_of_homMk_fac ((he i).symm.trans (hk i).symm)⟩

end SerrePositivity.InfinityCategories
