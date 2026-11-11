module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePath
public import Mathlib.Data.Finset.Sort

/-!
# 水平ステップの順序と第一座標の順位

概要：水平集合を順に列挙した番号は、そのステップ直前の第一座標に一致する。
方針：順序同型で開初区間を移し、有限集合の濃度を計算する。
規約：KST Construction A.5 の標準 shuffle。
使われ方：第一因子の面の番号から挿入すべき水平ステップを一意に選ぶ。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：水平ステップの列挙における順位はその直前の第一座標。
方針：水平集合の初区間を Fin p の初区間に順序同型で戻す。
規約：KST A.5、選んだステップは水平集合に属する。
使われ方：境界の面番号と水平ステップの対応。 -/
lemma ShuffleIndex.rank_eq_left {p n : ℕ} (s : ShuffleIndex p n) (a : s.val) :
    ((s.val.orderIsoOfFin s.property).symm a : ℕ) =
      (s.left.toOrderHom a.val.castSucc : ℕ) := by
  let e := s.val.orderIsoOfFin s.property
  let r := e.symm a
  have he : (Finset.Iio r).map (s.val.orderEmbOfFin s.property).toEmbedding =
      s.val.filter (fun j ↦ j < a.val) := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      rw [← hij]
      refine Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem _ _ _, ?_⟩
      change (e i).val < a.val
      have ht : e i < e r := e.strictMono (Finset.mem_Iio.mp hi)
      rw [e.apply_symm_apply] at ht
      exact ht
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hs, hja⟩
      refine Finset.mem_map.mpr ⟨e.symm ⟨j, hs⟩, ?_, ?_⟩
      · apply Finset.mem_Iio.mpr
        exact e.symm.strictMono hja
      · change (e (e.symm ⟨j, hs⟩)).val = j
        exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hs⟩)
  have hc := congrArg Finset.card he
  rw [Finset.card_map, Fin.card_Iio] at hc
  exact hc

/-- 概要：水平ステップを小さい順に列挙する実写像。
方針：濃度 p の有限集合の標準順序埋め込みを使う。
規約：KST A.5。使われ方：第一因子の内部の面を挿入位置へ送る。 -/
def ShuffleIndex.horizontalStep {p n : ℕ} (s : ShuffleIndex p n) : Fin p ↪o Fin n :=
  s.val.orderEmbOfFin s.property

/-- 概要：列挙した水平ステップは水平集合に属する。
方針：標準順序埋め込みの像の所属を使う。
規約：KST A.5。使われ方：水平挿入による同種ステップの面の構成。 -/
@[simp] lemma ShuffleIndex.horizontalStep_mem {p n : ℕ} (s : ShuffleIndex p n) (i : Fin p) :
    s.horizontalStep i ∈ s.val := Finset.orderEmbOfFin_mem _ _ _

/-- 概要：第 i 水平ステップ直前の第一座標は i。
方針：順位の濃度公式を標準列挙の像へ適用する。
規約：KST A.5、零から数える水平ステップ。
使われ方：各因子の境界の番号の復元。 -/
@[simp] lemma ShuffleIndex.horizontalStep_left {p n : ℕ} (s : ShuffleIndex p n) (i : Fin p) :
    (s.left.toOrderHom (s.horizontalStep i).castSucc : ℕ) = i := by
  let e := s.val.orderIsoOfFin s.property
  have ht := s.rank_eq_left (e i)
  change ((e.symm (e i)) : ℕ) = (s.left.toOrderHom (s.horizontalStep i).castSucc : ℕ) at ht
  rw [e.symm_apply_apply] at ht
  exact ht.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
