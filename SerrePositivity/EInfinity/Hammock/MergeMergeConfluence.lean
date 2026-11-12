module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMergeIndices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSurjectionComparison
public import SerrePositivity.EInfinity.Hammock.Reduction

/-!
# 元の二つの隣接合成の局所合流

概要：元の二つの同方向合成は、両側0〜1段で同じ未縮約対象へ到達する。
方針：単体圏の元の二重全射の合成則と、終域の色の回収を使う。
規約：元の語と全射列の等式であり、余極限内の値の一致では代用しない。
使われ方：基本縮約全体の局所合流。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {n : SimplexCategoryᵒᵖ}

lemma merge_merge_join_ordered {k : ℕ} (d : Fin (k + 3) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (i j : Fin (k + 1)) (hij : i ≤ j)
    (hi : d i.castSucc.castSucc = d i.castSucc.succ)
    (hj : d j.succ.castSucc = d j.succ.succ)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 3, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    ∃ q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n,
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d i.castSucc hi)).app n τ⟩ q ∧
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d j.succ hj)).app n τ⟩ q := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d i.castSucc hi
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d j.succ hj
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.merge_left_remaining_color d i j hij hi hj
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.merge_right_remaining_color d i j hij hi hj
  let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d i.castSucc).direction j hL
  let g' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d j.succ).direction i hR
  let σ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n τ
  let ρ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g).app n τ
  let q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n := ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f').app n σ⟩
  let q' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n := ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g').app n ρ⟩
  have hf : Function.Surjective (f ≫ f').orderHom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d i.castSucc).direction j hL).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap_surjective d i.castSucc hi)
  have hfg : ∀ x, Fin.cast rfl ((f ≫ f').orderHom x) = (g ≫ g').orderHom x := by
    intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.merge_predAbove_comp i j hij x
  have hq : q = q' := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_eq_of_surjections W X Y (f ≫ f') (g ≫ g') hf rfl hfg n τ
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at he
    change (⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f').app n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n τ)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) =
      ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g').app n
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g).app n τ)⟩ at he
    exact he
  refine ⟨q, Relation.ReflGen.single (Reduction.merge _ j hL σ), ?_⟩
  have hstep : Reduction W X Y n ⟨_, ρ⟩ q := by
    rw [hq]
    exact Reduction.merge _ i hR ρ
  exact Relation.ReflGen.single hstep

/-- 異なる二つの元の合成位置を、順序を保った標準の二重全射へ移す。 -/
lemma merge_merge_join_of_lt {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : Fin (k + 1)) (hpq : p < q)
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n,
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ r ∧
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d q hq)).app n τ⟩ r := by
  cases k with
  | zero =>
    have hp' := p.isLt
    have hq' := q.isLt
    change p.val < q.val at hpq
    omega
  | succ k =>
    let i : Fin (k + 1) := ⟨p.val, by have := q.isLt; change p.val < q.val at hpq; omega⟩
    let j : Fin (k + 1) := q.pred (Fin.ne_zero_of_lt hpq)
    have hi : i.castSucc = p := by apply Fin.ext; rfl
    have hj : j.succ = q := Fin.succ_pred q _
    have hij : i ≤ j := by
      change i.val ≤ j.val
      have he := congrArg Fin.val hj
      change j.val + 1 = q.val at he
      change p.val < q.val at hpq
      dsimp only [i]
      omega
    clear_value i j
    subst p
    subst q
    exact merge_merge_join_ordered W X Y d i j hij hp hq τ

/-- 同じ位置も含む二つの基本合成は、各側0〜1段で元の同じ対象へ合流する。 -/
lemma merge_merge_join {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : Fin (k + 1))
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n,
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ r ∧
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d q hq)).app n τ⟩ r := by
  rcases lt_trichotomy p q with h | h | h
  · exact merge_merge_join_of_lt W X Y d p q h hp hq τ
  · subst q
    exact ⟨_, Relation.ReflGen.refl, Relation.ReflGen.refl⟩
  · obtain ⟨r, hr, hs⟩ := merge_merge_join_of_lt W X Y d q p h hq hp τ
    exact ⟨r, hs, hr⟩

end SerrePositivity.EInfinity.Hammock
