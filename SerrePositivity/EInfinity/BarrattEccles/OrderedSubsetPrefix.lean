module

public import SerrePositivity.EInfinity.BarrattEccles.OrderedSubset

/-!
# 昇順部分集合の接頭辺数

概要：Berger–Fresse §1.1.3 の二段の shuffle の座標を、昇順部分集合の接頭要素数で計算する。
方針：昇順列挙の添字とその像の大小を、初期区間の濃度の不等式で比較する。
規約：切断位置は任意の自然数であり、辺集合内の要素自身は切断に含めない。
使われ方：三入力の shuffle の括弧付けの変更で各座標が保存されることを示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：昇順列挙の像が切断位置より前にあることは添字が接頭要素数より小さいことと同値である（Berger–Fresse §1.1.3）。
方針：添字の初期閉区間と初期開区間の濃度を接頭集合と比較する。
規約：列挙は濃度 k の集合 S の昇順列挙である。
使われ方：二段の shuffle の接頭辺数を合成して計算する。 -/
lemma orderEmbOfFin_lt_prefix {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k)
    (a : Fin k) (cut : ℕ) :
    (S.orderEmbOfFin hs a).val < cut ↔ a.val < (S.filter (fun x => x.val < cut)).card := by
  let e := S.orderEmbOfFin hs
  let F := Finset.univ.filter (fun b : Fin k => (e b).val < cut)
  have hcard : F.card = (S.filter (fun x => x.val < cut)).card := by
    apply Finset.card_bij (fun b _ => e b)
    · intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem S hs b, (Finset.mem_filter.mp hb).2⟩
    · intro b hb c hc hbc
      exact e.injective hbc
    · intro x hx
      let b := (S.orderIsoOfFin hs).symm ⟨x, (Finset.mem_filter.mp hx).1⟩
      have he : e b = x :=
        congrArg Subtype.val ((S.orderIsoOfFin hs).apply_symm_apply
          ⟨x, (Finset.mem_filter.mp hx).1⟩)
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
      rw [he]
      exact (Finset.mem_filter.mp hx).2
  constructor
  · intro hlt
    have hsub : Finset.Iic a ⊆ F := by
      intro b hb
      have hle := e.monotone (Finset.mem_Iic.mp hb)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change (e b).val ≤ (e a).val at hle
      change (e a).val < cut at hlt
      omega
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic, hcard] at hc
    omega
  · intro hlt
    by_contra ha
    have hsub : F ⊆ Finset.Iio a := by
      intro b hb
      apply Finset.mem_Iio.mpr
      apply lt_of_not_ge
      intro hab
      have hle := e.monotone hab
      have hbcut := (Finset.mem_filter.mp hb).2
      change (e a).val ≤ (e b).val at hle
      change ¬(e a).val < cut at ha
      omega
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio, hcard] at hc
    omega

/-- 概要：昇順に埋め込んだ部分集合の接頭濃度は小さい添字集合の接頭濃度で計算できる（Berger–Fresse §1.1.3）。
方針：map と filter を交換し、像の切断条件を添字と接頭要素数の比較へ直す。
規約：小さい部分集合 t は Fin k の部分集合である。
使われ方：三入力の shuffle の各座標を旗の辺集合の接頭濃度で表す。 -/
lemma orderedSubsetEquiv_prefix_card {N k : ℕ} (S : Finset (Fin N)) (hs : S.card = k)
    (t : Finset (Fin k)) (cut : ℕ) :
    (((orderedSubsetEquiv S hs) t).val.filter (fun x => x.val < cut)).card =
      (t.filter (fun a => a.val < (S.filter (fun x => x.val < cut)).card)).card := by
  change ((t.map (S.orderEmbOfFin hs).toEmbedding).filter (fun x => x.val < cut)).card = _
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact orderEmbOfFin_lt_prefix S hs a cut

end SerrePositivity.EInfinity.BarrattEccles
