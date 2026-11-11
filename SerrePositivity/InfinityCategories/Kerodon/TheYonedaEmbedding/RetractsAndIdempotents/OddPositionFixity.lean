module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingOddRank
public import Mathlib.Order.Preorder.Finite

/-!
概要：同じ元の交互セル内では、全奇数位置を通る単体の元の奇数位置の対応は恒等。
方針：元の位置の単射の証人を使い、順序自己写像の単調性と有限性を適用する。
規約：元の位置 v と両列の値を保持し、位置対応を未証明の入力に仮定しない。
使われ方：境界外の元の全セルの単射性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の奇数位置の順序は、選んだ元の定義域の位置でも厳密に保たれる。 -/
lemma oddPositionSelection_strictMono {m n : ℕ} (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (v : Fin m → Fin (n + 1)) (hv : ∀ i, (a (v i)).val = 2 * i.val + 1) : StrictMono v := by
  intro i j hij
  by_contra hn
  have hpos : v j ≤ v i := le_of_not_gt hn
  have ha := stdSimplex.monotone_apply a hpos
  change (a (v j)).val ≤ (a (v i)).val at ha
  rw [hv j, hv i] at ha
  have hij' : i.val < j.val := hij
  omega

/-- 同じ元のセルでは、元の全奇数位置を両列で同じ値のまま回収する証人が存在する。 -/
lemma alternatingCell_odd_positions_fixed_exists {m n : ℕ}
    (a b : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) b)
    (hhit : ∀ i : Fin m, ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1) :
    ∃ v : Fin m → Fin (n + 1), (∀ i, (a (v i)).val = 2 * i.val + 1) ∧
      ∀ i, (b (v i)).val = 2 * i.val + 1 := by
  obtain ⟨f, hf, v, hva, hvb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_odd_injection_exists a b h hhit
  have hv := oddPositionSelection_strictMono a v hva
  have hmono : Monotone f := by
    intro i j hij
    have hb := stdSimplex.monotone_apply b (hv.monotone hij)
    change (b (v i)).val ≤ (b (v j)).val at hb
    rw [hvb i, hvb j] at hb
    change (f i).val ≤ (f j).val
    omega
  have he : f = id := (hmono.strictMono_of_injective hf).eq_id
  refine ⟨v, hva, ?_⟩
  intro i
  have hb := hvb i
  rw [he] at hb
  exact hb

/-- 元の全セル像の等式と固定した全奇数位置から、元の任意の奇数位置を回収する。 -/
lemma alternatingCell_equal_odd_of_fixed_positions {m n : ℕ}
    (a b : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) b)
    (v : Fin m → Fin (n + 1))
    (hva : ∀ i, (a (v i)).val = 2 * i.val + 1)
    (hvb : ∀ i, (b (v i)).val = 2 * i.val + 1)
    (p : Fin (n + 1)) (hp : (a p).val % 2 = 1) : a p = b p := by
  let i : Fin m := ⟨(a p).val / 2, by have ha := (a p).isLt; omega⟩
  have ha : a p = a (v i) := by
    apply Fin.ext
    rw [hva i]
    change (a p).val = 2 * ((a p).val / 2) + 1
    omega
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_equal_indices h.symm p (v i) hp ha
  have hvEq : a (v i) = b (v i) := Fin.ext ((hva i).trans (hvb i).symm)
  exact (ha.trans hvEq).trans hb.symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
