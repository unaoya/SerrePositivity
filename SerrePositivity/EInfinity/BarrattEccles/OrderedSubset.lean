module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Preimage

/-!
# 有限な順序集合の部分集合の昇順での添字替え

概要：Berger–Fresse §1.1.3 の反復 shuffle の添字替えに使う部分集合の対応を構成する。
方針：大きい辺集合の昇順列挙による map と preimage を互いの逆とする。
規約：部分集合の濃度は保存され、頂点の順序は昇順列挙から継承する。
使われ方：二段の shuffle を二つの辺集合の包含の旗で表す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：昇順列挙の小さい添字集合の部分集合と元の集合に含まれる部分集合の同値（Berger–Fresse §1.1.3）。
方針：昇順埋め込みによる map と preimage を用いる。
規約：元の集合 S は Fin N に属し、その濃度は k である。
使われ方：反復 shuffle の小さい経路を大きい辺集合の部分集合として表す。 -/
def orderedSubsetEquiv {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k) :
    Finset (Fin k) ≃ {T : Finset (Fin N) // T ⊆ S} where
  toFun t := ⟨t.map (S.orderEmbOfFin hs).toEmbedding, by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.orderEmbOfFin_mem S hs a⟩
  invFun t := t.val.preimage (S.orderEmbOfFin hs) (S.orderEmbOfFin hs).injective.injOn
  left_inv t := Finset.preimage_map (S.orderEmbOfFin hs).toEmbedding t
  right_inv t := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp ha
    · intro hx
      let a := (S.orderIsoOfFin hs).symm ⟨x, t.property hx⟩
      have he : S.orderEmbOfFin hs a = x :=
        congrArg Subtype.val ((S.orderIsoOfFin hs).apply_symm_apply ⟨x, t.property hx⟩)
      refine Finset.mem_map.mpr ⟨a, Finset.mem_preimage.mpr ?_, he⟩
      rw [he]
      exact hx

/-- 概要：昇順の部分集合の添字替えは濃度を保存する（Berger–Fresse §1.1.3）。
方針：埋め込みによる有限集合の map の濃度の保存を使う。
規約：任意の小さい部分集合で成り立つ。
使われ方：三入力の shuffle の各色の辺数を保つ。 -/
lemma orderedSubsetEquiv_card {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k)
    (t : Finset (Fin k)) : ((orderedSubsetEquiv S hs) t).val.card = t.card :=
  Finset.card_map _

/-- 概要：昇順の添字への逆変換も濃度を保存する（Berger–Fresse §1.1.3）。
方針：順変換の濃度の保存と同値の逆性を使う。
規約：部分集合 t は S に含まれる。
使われ方：辺集合の旗から小さい shuffle 経路を復元する。 -/
lemma orderedSubsetEquiv_symm_card {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k)
    (t : {T : Finset (Fin N) // T ⊆ S}) : ((orderedSubsetEquiv S hs).symm t).card = t.val.card := by
  have h := (orderedSubsetEquiv_card S hs ((orderedSubsetEquiv S hs).symm t)).symm
  rw [(orderedSubsetEquiv S hs).apply_symm_apply] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
