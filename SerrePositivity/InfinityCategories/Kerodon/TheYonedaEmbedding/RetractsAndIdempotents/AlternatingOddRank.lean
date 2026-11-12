module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingScalar
public import Mathlib.Data.Fintype.Card

/-!
概要：元の全奇数頂点を通る交互セルの単体は、短い元の交互セルへ入らない。
方針：元の射の値を保つ異なる奇数位置の単射を構成し、元の有限位置数を比較する。
規約：元の全セル像の等式を使用し、対象列の偶奇だけから単射性を仮定しない。
使われ方：Ret の前段階の逆像が元のセル境界に入る逆包含。

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

/-- 元の全奇数位置の像を同じまま保つ、短い列の奇数位置への元の単射が存在する。 -/
lemma alternatingCell_odd_injection_exists {m M n : ℕ}
    (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌) (b : (Δ[2 * M] : SSet.{u}) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M).app (Opposite.op ⦋n⦌) b)
    (hhit : ∀ i : Fin m, ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1) :
    ∃ f : Fin m → Fin M, Function.Injective f ∧ ∃ v : Fin m → Fin (n + 1),
      (∀ i, (a (v i)).val = 2 * i.val + 1) ∧
        ∀ i, (b (v i)).val = 2 * (f i).val + 1 := by
  classical
  choose v hv using hhit
  have hbodd : ∀ i, (b (v i)).val % 2 = 1 := by
    intro i
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_equal_source_iff h (v i)).mp
    rw [hv i]
    omega
  let f : Fin m → Fin M := fun i ↦ ⟨(b (v i)).val / 2, by
    have hb := (b (v i)).isLt
    have hodd := hbodd i
    omega⟩
  have hf : Function.Injective f := by
    intro i j he
    have hdiv := congrArg Fin.val he
    change (b (v i)).val / 2 = (b (v j)).val / 2 at hdiv
    have he' : b (v i) = b (v j) := by
      apply Fin.ext
      have hi := hbodd i
      have hj := hbodd j
      omega
    have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_equal_indices h (v i) (v j) (hbodd i) he'
    have hav := congrArg Fin.val ha
    rw [hv i, hv j] at hav
    apply Fin.ext
    omega
  refine ⟨f, hf, v, hv, ?_⟩
  intro i
  change (b (v i)).val = 2 * ((b (v i)).val / 2) + 1
  have hi := hbodd i
  omega

/-- 元の全奇数位置を通るセルの単体が同じ像を持つなら、標的の奇数位置数は減らせない。 -/
lemma alternatingCell_odd_rank_le {m M n : ℕ}
    (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌) (b : (Δ[2 * M] : SSet.{u}) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M).app (Opposite.op ⦋n⦌) b)
    (hhit : ∀ i : Fin m, ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1) : m ≤ M := by
  obtain ⟨f, hf, _⟩ := alternatingCell_odd_injection_exists a b h hhit
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin] using hc

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
