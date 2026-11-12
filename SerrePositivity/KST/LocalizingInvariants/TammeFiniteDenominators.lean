module

public import SerrePositivity.KST.LocalizingInvariants.TammeDenominatorClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiniteCofiberDenominators
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiniteCofiberEqualization

/-!
概要：元の Tamme 分母の有限族に実共通分母と共有合成二単体を構成する。
方針：元の核の安定閉包との一致で、既存の有限分母・均等化を同じ集合へ戻す。
規約：入力辺と共有合成辺を保持。全次元の相対境界充填は後続。
使われ方：一般商への有限図式の移送。
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
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma tammeLocalizingEdges_iff_trW {x y : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) x y) :
    f.edge ∈ tammeLocalizingEdges p q ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q))).trW
        (SSet.Truncated.HomotopyCategory.homMk f) := by
  rw [← tammeLocalizingEdges_stableClosure]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW _ f

lemma tammeLocalizingEdges_commonDenominator {n : ℕ} {x : (laxCategory p q).obj _⦋0⦌}
    (y : Fin n → (laxCategory p q).obj _⦋0⦌)
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) (y i) x)
    (hs : ∀ i, (s i).edge ∈ tammeLocalizingEdges p q) :
    ∃ (a : (laxCategory p q).obj _⦋0⦌)
      (t : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a x),
      t.edge ∈ tammeLocalizingEdges p q ∧
      ∃ r : ∀ i, Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a (y i),
        ∀ i, (r i).edge ∈ tammeLocalizingEdges p q ∧
          Nonempty (Truncated.Edge.CompStruct (r i) (s i) t) := by
  have hs' : ∀ i, (s i).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)) z} := by
    simpa only [tammeLocalizingEdges_stableClosure] using hs
  simpa only [tammeLocalizingEdges_stableClosure] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_commonDenominator (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)) y s hs'

lemma tammeLocalizingEdges_equalizeFinite {n : ℕ} {x : (laxCategory p q).obj _⦋0⦌}
    {y z : Fin n → (laxCategory p q).obj _⦋0⦌}
    (f g : ∀ i, Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) x (y i))
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) (y i) (z i))
    (hs : ∀ i, (s i).edge ∈ tammeLocalizingEdges p q)
    (h : ∀ i, SSet.Truncated.HomotopyCategory.homMk (f i) ≫
      SSet.Truncated.HomotopyCategory.homMk (s i) =
        SSet.Truncated.HomotopyCategory.homMk (g i) ≫
          SSet.Truncated.HomotopyCategory.homMk (s i)) :
    ∃ (a : (laxCategory p q).obj _⦋0⦌)
      (t : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a x),
      t.edge ∈ tammeLocalizingEdges p q ∧
      ∃ k : ∀ i, Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a (y i),
        ∀ i, Nonempty (Truncated.Edge.CompStruct t (f i) (k i)) ∧
          Nonempty (Truncated.Edge.CompStruct t (g i) (k i)) := by
  have hs' : ∀ i, (s i).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {a | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)) a} := by
    simpa only [tammeLocalizingEdges_stableClosure] using hs
  simpa only [tammeLocalizingEdges_stableClosure] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_equalizeFinite (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)) f g s hs' h

end SerrePositivity.KST.LocalizingInvariants
