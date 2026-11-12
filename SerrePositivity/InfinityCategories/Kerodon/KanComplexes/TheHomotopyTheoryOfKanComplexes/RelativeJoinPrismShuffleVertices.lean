module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismShuffle

/-!
概要：prism の最大単体の頂点の式と単射性。
方針：時刻と係数の和から元の頂点番号を回復する。
規約：区間は第一因子、切替位置は k。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） のホーンの貼り合わせ。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：最大単体の時刻が零であるのは切替位置以下の頂点。
方針：標準区間の単体の切替位置の式を使う。
規約：頂点番号は m+2 個、係数の頂点は m+1 個。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、最大単体の面の分類。 -/
lemma relativeJoinPrismShuffle_time_zero_iff (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 i).val = 0 ↔ i ≤ k.castSucc := by
  change (stdSimplex.objMk₁.{u} k.succ.castSucc i).val = 0 ↔ _
  have he : (stdSimplex.objMk₁.{u} k.succ.castSucc i).val = 0 ↔
      stdSimplex.objMk₁.{u} k.succ.castSucc i = 0 :=
    ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
  rw [he, stdSimplex.objMk₁_apply_eq_zero_iff]
  change i.val < k.val + 1 ↔ i.val ≤ k.val
  omega

/-- 概要：最大単体の係数の頂点番号は切替前では元の番号、後では一を引いた番号。
方針：退化の順序写像 predAbove の二つの場合を計算する。
規約：k の係数頂点は切替の前後で重複する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、境界の逆像の頂点計算。 -/
lemma relativeJoinPrismShuffle_coefficient_val (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 i).val =
      if i ≤ k.castSucc then i.val else i.val - 1 := by
  change (k.predAbove i).val = _
  by_cases hi : i ≤ k.castSucc
  · rw [ite_eq_left hi, Fin.predAbove_of_le_castSucc k i hi]
    rfl
  · rw [ite_eq_right hi, Fin.predAbove_of_castSucc_lt k i (lt_of_not_ge hi)]
    rfl

/-- 概要：最大単体の時刻と係数の頂点番号の和は元の頂点番号。
方針：切替前と後で時刻の値と係数の値を計算する。
規約：時刻を自然数零または一として読む。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、最大単体の単射性。 -/
lemma relativeJoinPrismShuffle_vertex_sum (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 i).val +
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 i).val = i.val := by
  rw [relativeJoinPrismShuffle_coefficient_val]
  have ht := ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 i).isLt
  by_cases hi : i ≤ k.castSucc
  · rw [ite_eq_left hi, (relativeJoinPrismShuffle_time_zero_iff m k i).mpr hi, zero_add]
  · rw [ite_eq_right hi]
    have hz := (relativeJoinPrismShuffle_time_zero_iff.{u} m k i).not.mpr hi
    have hik : k.val < i.val := lt_of_not_ge hi
    omega

/-- 概要：最大単体の頂点から時刻と係数への写像は単射。
方針：二つの成分の和で頂点番号を回復する。
規約：頂点の単射性を型の意味で結論する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、セルの characteristic map の単射性。 -/
lemma relativeJoinPrismShuffle_vertex_injective (m : ℕ) (k : Fin (m + 1)) :
    Function.Injective (fun i : Fin (m + 2) ↦
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).1 i, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k).2 i)) := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun p : Fin 2 × Fin (m + 1) ↦ p.1.val + p.2.val) h
  simpa only [relativeJoinPrismShuffle_vertex_sum] using he

/-- 概要：prism の最大単体の characteristic map は単射。
方針：各次数の順序写像を全頂点で比較し、最大単体の頂点の単射性を使う。
規約：通常の単体集合の射の Mono を結論する。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、ホーンを貼る pushout の逆像の計算。 -/
instance relativeJoinPrismShuffle_mono (m : ℕ) (k : Fin (m + 1)) :
    Mono (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle.{u} m k)) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro a b h
  apply stdSimplex.ext
  intro i
  apply relativeJoinPrismShuffle_vertex_injective.{u} m k
  have he := congrArg (fun z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌ ↦ (z.1 i, z.2 i)) h
  exact he

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
