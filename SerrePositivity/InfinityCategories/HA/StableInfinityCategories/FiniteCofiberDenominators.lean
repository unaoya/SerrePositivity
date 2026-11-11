module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiniteHoDenominators
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 有限族の実共通分母と合成二単体

概要：同じ終点を持つ有限個の実 Verdier 分母を一つの実辺で同時に細分する。
方針：h C の共通分母を実辺に戻し、各因子分解を実合成二単体へ持ち上げる。
規約：全入力辺と共通分母を厳密に保持する。使われ方：有限族の分数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 有限個の実分母には、一つの実共通分母と各因子分解の実二単体が存在する。 -/
theorem cofiberStableEdges_commonDenominator (P : Set (X _⦋0⦌))
    {n : ℕ} {x : X _⦋0⦌} (y : Fin n → X _⦋0⦌)
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj X) (y i) x)
    (hs : ∀ i, (s i).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z}) :
    ∃ (q : X _⦋0⦌) (t : Truncated.Edge (X := (truncation 2).obj X) q x),
      t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ∧
      ∃ r : ∀ i, Truncated.Edge (X := (truncation 2).obj X) q (y i),
        ∀ i, (r i).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ∧
          Nonempty (Truncated.Edge.CompStruct (r i) (s i) t) := by
  obtain ⟨q, t, ht, r, hr⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_commonDenominator P
    (fun i => SSet.HomotopyCategory.mk (y i))
    (fun i => SSet.Truncated.HomotopyCategory.homMk (s i))
    (fun i => (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW P (s i)).mp (hs i))
  obtain ⟨q, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective q
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective q x t
  choose r' hr' using fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective q (y i) (r i)
  have ht' := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW P t).mpr ht
  refine ⟨q, t, ht', r', ?_⟩
  intro i
  have hc : Nonempty (Truncated.Edge.CompStruct (r' i) (s i) t) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
    rw [hr' i]
    exact hr i
  exact ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_compStruct_twoOfThree P hc.some).2.2 (hs i) ht', hc⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
