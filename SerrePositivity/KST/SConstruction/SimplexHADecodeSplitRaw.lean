module
public import SerrePositivity.KST.SConstruction.SimplexHASplitRawRecursion
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorConcat

/-! # 元の内部一端点挿入の生の HA 値の左右分解
概要：任意の右側生成元・右側集合を保ち、内部一端点の値を同じ左右合成値へ戻す。
方針：元の右ブロックの三再帰と、左右合成値の同じ再帰を照合する。
規約：元の切断頂点と全自由座標を保持。使われ方：全座標の一面への線形復元の制限。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の零右次元の左右合成値は、同じ左生成元と元の tail 値の合成。 -/
lemma simplexHASplitRawValue_zero_right {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n : ℕ) (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex 0)
    (v : Fin (n + 1 + 0 + 1) ↪o Fin (N + 1))
    (T : Finset (Fin (N + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last (n + 1)) < r) :
    HEq (simplexHASplitRawValue A s n i 0 j v T hT hb)
      (forward A (n := -((serreCubeGeneratorFreeDimension n i + (T.card - 1) : ℕ) : ℤ))
        (simplexHABeadWordRawValue A s (simplexHAGeneratorWord n i
          (Fin.castSuccOrderEmb.trans v) (v (Fin.last (n + 1))) (simplexHADecodePrefix_last n v)))
        (simplexHABeadWordRawValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (n + 1))) hb))
        (by omega)) := by
  have hp := Finset.card_pos.mpr hT
  have hR := simplexHABeadWordDecode_zero_rawTail A s j (simplexHASplitRight n 0 v) T hT
    (fun r hr => lt_of_eq_of_lt (simplexHASplitRight_last n 0 v) (hb r hr))
  exact dgForward_heq A rfl rfl rfl rfl
    (show -((serreCubeGeneratorFreeDimension 0 j + T.card - 1 : ℕ) : ℤ) =
      -((T.card - 1 : ℕ) : ℤ) by simp only [serreCubeGeneratorFreeDimension, zero_add])
    (show -((serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension 0 j +
      T.card - 1 : ℕ) : ℤ) =
        -((serreCubeGeneratorFreeDimension n i + (T.card - 1) : ℕ) : ℤ) by
          change -((serreCubeGeneratorFreeDimension n i + 0 + T.card - 1 : ℕ) : ℤ) = _
          omega) _ _ _ _ _ _ HEq.rfl hR

/-- 元の内部一端点を持つ全生成元の生の値は、元の同じ左右の HA 合成値。 -/
lemma simplexHABeadWordDecode_split_one_rawValue {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n : ℕ) (i : SerreCubeGeneratorIndex n) (m : ℕ) (j : SerreCubeGeneratorIndex m)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1))
    (T : Finset (Fin (N + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last (n + 1 + m)) < r) :
    HEq (simplexHABeadWordRawValue A s
      (simplexHABeadWordDecode (n + 1 + m)
        (serreCubeGeneratorConcat (n + 1) (i, 1) m j) v T hT hb))
      (simplexHASplitRawValue A s n i m j v T hT hb) := by
  induction m generalizing T with
  | zero =>
    have h := simplexHABeadWordDecode_one_rawValue A s n i v T hT hb
    exact h.trans (simplexHASplitRawValue_zero_right A s n i j v T hT hb).symm
  | succ m ih =>
    obtain ⟨j, l⟩ := j
    let g := serreCubeGeneratorConcat (n + 1) (i, 1) m j
    let vp := Fin.castSuccOrderEmb.trans v
    have hfree : serreCubeGeneratorFreeDimension (n + 1 + m) g =
        serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension m j :=
      serreCubeGeneratorConcat_freeDimension (n + 1) (i, 1) m j
    refine Fin.cases ?_ (Fin.cases ?_ (fun l => ?_)) l
    · have h₀ := simplexHABeadWordDecode_zero_rawValue A s (n + 1 + m) g v T hT hb
      have h₁ := ih j vp T hT (simplexHADecodePrefix_tail (n + 1 + m) v T hb)
      exact (heq_of_eq h₀).trans (h₁.trans
        (heq_of_eq (simplexHASplitRawValue_zero A s n i m j v T hT hb)).symm)
    · let r := v (Fin.last (n + 1 + (m + 1)))
      let Q := simplexHABeadWordRawValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb)
      have h₀ := simplexHABeadWordDecode_one_rawValue A s (n + 1 + m) g v T hT hb
      have h₁ := ih j vp {r} (Finset.singleton_nonempty r)
        (simplexHADecodePrefix_cut (n + 1 + m) v)
      have h₂ := dgForward_heq A rfl rfl rfl
        (congrArg (fun d : ℕ => -(d : ℤ)) hfree) rfl
        (congrArg (fun d : ℕ => -((d + (T.card - 1) : ℕ) : ℤ)) hfree)
        _ _ Q Q (by omega) (by
          simp only [Nat.cast_add]
          omega) h₁ HEq.rfl
      exact h₀.trans (h₂.trans (simplexHASplitRawValue_one A s n i m j v T hT hb).symm)
    · have h₀ := simplexHABeadWordDecode_edge_rawValue A s (n + 1 + m) g v T hT hb
      have h₁ := ih j vp (insert (v (Fin.last (n + 1 + (m + 1)))) T)
        (Finset.insert_nonempty _ T) (simplexHADecodePrefix_insert (n + 1 + m) v T hb)
      exact h₀.trans (h₁.trans (simplexHASplitRawValue_edge A s n i m j v T hT hb).symm)

end SerrePositivity.KST.SConstruction
