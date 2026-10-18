module

public import SerrePositivity.EInfinity.BarrattEccles.OrderedSubset

/-!
# 昇順部分集合の列挙の合成

概要：Berger–Fresse §1.1.3 の反復 shuffle の辺の列挙を比較する。
方針：昇順埋め込みの像の列挙を、一意性から列挙の合成と同定する。
規約：集合差は元の有限辺集合の中で取る。
使われ方：三入力の二つの括弧付けの shuffle 置換と符号を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：昇順埋め込みによる像の列挙は列挙の合成である（Berger–Fresse §1.1.3）。
方針：像への所属と狭義単調性から昇順列挙の一意性を使う。
規約：像の濃度の証明は任意に指定できる。
使われ方：有限辺集合の次数移送と部分集合の反復列挙を計算する。 -/
lemma orderEmbOfFin_map_orderEmbedding {N M k : ℕ} (S : Finset (Fin N))
    (hs : S.card = k) (e : Fin N ↪o Fin M)
    (ht : (S.map e.toEmbedding).card = k) (i : Fin k) :
    (S.map e.toEmbedding).orderEmbOfFin ht i = e (S.orderEmbOfFin hs i) := by
  have h := Finset.orderEmbOfFin_unique ht
    (f := fun a => e (S.orderEmbOfFin hs a))
    (fun a => Finset.mem_map.mpr ⟨_, S.orderEmbOfFin_mem hs a, rfl⟩)
    (e.strictMono.comp (S.orderEmbOfFin hs).strictMono)
  exact (congrFun h i).symm

/-- 概要：昇順部分集合の列挙は二つの昇順列挙の合成である（Berger–Fresse §1.1.3）。
方針：昇順埋め込みの像の列挙の公式を適用する。
規約：大きい集合の濃度を k、小さい集合の濃度を l とする。
使われ方：反復 shuffle の各色の辺番号を計算する。 -/
lemma orderedSubsetEquiv_enumeration {N k l : ℕ} (S : Finset (Fin N))
    (hs : S.card = k) (t : Finset (Fin k)) (ht : t.card = l) (i : Fin l) :
    ((orderedSubsetEquiv S hs) t).val.orderEmbOfFin
        ((orderedSubsetEquiv_card S hs t).trans ht) i =
      S.orderEmbOfFin hs (t.orderEmbOfFin ht i) :=
  orderEmbOfFin_map_orderEmbedding t ht (S.orderEmbOfFin hs) _ i

/-- 概要：小さい添字集合の補集合は大きい集合内の集合差に対応する（Berger–Fresse §1.1.3）。
方針：像集合の所属を埋め込みの単射性と全射性で比較する。
規約：左辺の補集合は Fin k、右辺の集合差は Fin N で取る。
使われ方：三入力の二番目の色の辺集合を同定する。 -/
lemma orderedSubsetEquiv_compl {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k)
    (t : Finset (Fin k)) :
    ((orderedSubsetEquiv S hs) tᶜ).val = S \ ((orderedSubsetEquiv S hs) t).val := by
  ext x
  change x ∈ tᶜ.map (S.orderEmbOfFin hs).toEmbedding ↔
    x ∈ S \ t.map (S.orderEmbOfFin hs).toEmbedding
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_sdiff.mpr ⟨S.orderEmbOfFin_mem hs a, ?_⟩
    intro hm
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hm
    have he : b = a := (S.orderEmbOfFin hs).injective hba
    exact (Finset.mem_compl.mp ha) (he ▸ hb)
  · intro hx
    obtain ⟨hxS, hxt⟩ := Finset.mem_sdiff.mp hx
    let a := (S.orderIsoOfFin hs).symm ⟨x, hxS⟩
    have ha : S.orderEmbOfFin hs a = x :=
      congrArg Subtype.val ((S.orderIsoOfFin hs).apply_symm_apply ⟨x, hxS⟩)
    refine Finset.mem_map.mpr ⟨a, Finset.mem_compl.mpr ?_, ha⟩
    intro hat
    exact hxt (Finset.mem_map.mpr ⟨a, hat, ha⟩)

/-- 概要：同じ像集合をもつ二つの昇順列挙は一致する（Berger–Fresse §1.1.3）。
方針：両方の列挙を共通の像集合の一意な昇順列挙と比較する。
規約：元の辺集合の台の濃度は異なってよい。
使われ方：反復 shuffle の各色の辺の列挙を直接比較する。 -/
lemma orderEmbOfFin_eq_of_map_eq {N M K k : ℕ} (S : Finset (Fin N))
    (T : Finset (Fin M)) (hs : S.card = k) (ht : T.card = k)
    (e : Fin N ↪o Fin K) (f : Fin M ↪o Fin K)
    (h : S.map e.toEmbedding = T.map f.toEmbedding) (i : Fin k) :
    e (S.orderEmbOfFin hs i) = f (T.orderEmbOfFin ht i) := by
  have hm := Finset.orderEmbOfFin_unique
    (s := T.map f.toEmbedding) (by simpa using ht)
    (f := fun a => e (S.orderEmbOfFin hs a))
    (fun a => h ▸ Finset.mem_map.mpr ⟨_, S.orderEmbOfFin_mem hs a, rfl⟩)
    (e.strictMono.comp (S.orderEmbOfFin hs).strictMono)
  exact (congrFun hm i).trans
    (orderEmbOfFin_map_orderEmbedding T ht f _ i)

end SerrePositivity.EInfinity.BarrattEccles
