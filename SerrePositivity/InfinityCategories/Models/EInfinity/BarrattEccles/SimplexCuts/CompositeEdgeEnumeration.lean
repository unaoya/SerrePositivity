module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeMixedEdgeOrder
public import Mathlib.Data.Fintype.EquivFin

/-!
模型。文献の定義との比較は後で
# 同じ合成語の全水平辺を両種の辺で列挙する

Berger–Fresse §2.2.6、M14 L12a の逆復元。
元の外側境界と内側内部辺を合わせ、重複しない同じ有限濃度から全辺を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の外側境界と内側内部辺の位置写像の和（BF §2.2.6）。 -/
def compositeEdgeSum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Fin (m + d) ⊕ Fin (n + e) → Fin (m + n + (d + e)) :=
  Sum.elim (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k r)

/-- C428：元の両種の辺の列挙は重複しない（BF §2.2.6）。 -/
lemma compositeEdgeSum_injective {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeEdgeSum u v k r) := by
  have hne (i : Fin (m + d)) (a : Fin (n + e)) :
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k r i ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k r a := by
    have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerOuterEdge_order u v k r a i
    by_cases hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val)).val ≤ i.val
    · exact ne_of_gt (ho.1 hp)
    · exact ne_of_lt (ho.2 (lt_of_not_ge hp))
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge_strictMono u v k r).injective he)
    | inr a => exact False.elim (hne i a he)
  | inr a =>
    cases y with
    | inl i => exact False.elim (hne i a he.symm)
    | inr b => exact congrArg Sum.inr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge_strictMono u v k r).injective he)

/-- C429：同じ両種の辺の列挙は、元の全合成水平辺を覆う（BF §2.2.6）。 -/
lemma compositeEdgeSum_bijective {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeEdgeSum u v k r) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeEdgeSum_injective u v k r, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
