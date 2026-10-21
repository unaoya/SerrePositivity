module

public import SerrePositivity.KST.LocalizingInvariants.TammeArrowDenominators
public import SerrePositivity.InfinityCategories.Stable.FiniteCofiberDenominators
public import SerrePositivity.InfinityCategories.Stable.FiniteCofiberEqualization

/-!
概要：元の矢印圏の分母の有限族は、同じ点ごとの分母による共通細分と均等化を持つ。
方針：真の核の安定閉包との一致を使い、安定な矢印圏の実分母計算を適用する。
規約：矢印図式間の辺と共有合成二単体を保持する。商側の局所化普遍性は未主張。
使われ方：指定四角形とそのホモトピーを保つ相対分数計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeArrowLocalizingEdges_commonDenominator {n : ℕ}
    {x : (stableArrowCategory (laxCategory p q)).obj _⦋0⦌}
    (y : Fin n → (stableArrowCategory (laxCategory p q)).obj _⦋0⦌)
    (s : ∀ i, Truncated.Edge
      (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) (y i) x)
    (hs : ∀ i, (s i).edge ∈ tammeArrowLocalizingEdges p q) :
    ∃ (a : (stableArrowCategory (laxCategory p q)).obj _⦋0⦌)
      (t : Truncated.Edge
        (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) a x),
      t.edge ∈ tammeArrowLocalizingEdges p q ∧
      ∃ r : ∀ i, Truncated.Edge
        (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) a (y i),
        ∀ i, (r i).edge ∈ tammeArrowLocalizingEdges p q ∧
          Nonempty (Truncated.Edge.CompStruct (r i) (s i) t) := by
  have hs' : ∀ i, (s i).edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (tammeArrowKernel p q) v} := by
    simpa only [tammeArrowLocalizingEdges_stableClosure] using hs
  simpa only [tammeArrowLocalizingEdges_stableClosure] using
    cofiberStableEdges_commonDenominator (tammeArrowKernel p q) y s hs'

lemma tammeArrowLocalizingEdges_equalizeFinite {n : ℕ}
    {x : (stableArrowCategory (laxCategory p q)).obj _⦋0⦌}
    {y z : Fin n → (stableArrowCategory (laxCategory p q)).obj _⦋0⦌}
    (f g : ∀ i, Truncated.Edge
      (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) x (y i))
    (s : ∀ i, Truncated.Edge
      (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) (y i) (z i))
    (hs : ∀ i, (s i).edge ∈ tammeArrowLocalizingEdges p q)
    (h : ∀ i, SSet.Truncated.HomotopyCategory.homMk (f i) ≫
      SSet.Truncated.HomotopyCategory.homMk (s i) =
        SSet.Truncated.HomotopyCategory.homMk (g i) ≫
          SSet.Truncated.HomotopyCategory.homMk (s i)) :
    ∃ (a : (stableArrowCategory (laxCategory p q)).obj _⦋0⦌)
      (t : Truncated.Edge
        (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) a x),
      t.edge ∈ tammeArrowLocalizingEdges p q ∧
      ∃ k : ∀ i, Truncated.Edge
        (X := (truncation 2).obj (stableArrowCategory (laxCategory p q)).obj) a (y i),
        ∀ i, Nonempty (Truncated.Edge.CompStruct t (f i) (k i)) ∧
          Nonempty (Truncated.Edge.CompStruct t (g i) (k i)) := by
  have hs' : ∀ i, (s i).edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (tammeArrowKernel p q) v} := by
    simpa only [tammeArrowLocalizingEdges_stableClosure] using hs
  simpa only [tammeArrowLocalizingEdges_stableClosure] using
    cofiberStableEdges_equalizeFinite (tammeArrowKernel p q) f g s hs' h

end SerrePositivity.KST.LocalizingInvariants
