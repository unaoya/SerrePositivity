module
public import SerrePositivity.KST.SConstruction.SimplexHASplitRawValue
public import SerrePositivity.KST.SConstruction.SimplexHADecodeRawValues

/-! # 元の内部切断の左右合成値の右ブロック再帰
概要：右ブロックの零・一端点と辺の作用を、同じ左右合成値で回収する。
方針：元の読み替えの再帰と豊穣順合成の結合則を使う。
規約：元の右側集合と因子順を保持。使われ方：任意位置の一端点挿入の生の値の一致。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
variable {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N) (n : ℕ) (i : SerreCubeGeneratorIndex n)
  (m : ℕ) (j : SerreCubeGeneratorIndex m)
  (v : Fin (n + 1 + (m + 1) + 1) ↪o Fin (N + 1))
  (T : Finset (Fin (N + 1))) (hT : T.Nonempty)
  (hb : ∀ r ∈ T, v (Fin.last (n + 1 + (m + 1))) < r)

/-- 元の右ブロックの零端点は、元の最右頂点を除く同じ左右合成値。 -/
lemma simplexHASplitRawValue_zero :
    simplexHASplitRawValue A s n i (m + 1) (j, 0) v T hT hb =
      simplexHASplitRawValue A s n i m j (Fin.castSuccOrderEmb.trans v) T hT
        (simplexHADecodePrefix_tail (n + 1 + m) v T hb) := by
  have h := simplexHABeadWordDecode_zero_rawValue A s m j (simplexHASplitRight n (m + 1) v)
    T hT (fun r hr => lt_of_eq_of_lt (simplexHASplitRight_last n (m + 1) v) (hb r hr))
  unfold simplexHASplitRawValue
  exact eq_of_heq (dgForward_heq A rfl rfl rfl rfl rfl rfl _ _ _ _ _ _ HEq.rfl (heq_of_eq h))

/-- 元の右ブロックの一端点は、前段の左右合成値と元の同じ tail 値の合成。 -/
lemma simplexHASplitRawValue_one :
    HEq (simplexHASplitRawValue A s n i (m + 1) (j, 1) v T hT hb)
      (forward A
        (n := -((serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension m j +
          (T.card - 1) : ℕ) : ℤ))
        (simplexHASplitRawValue A s n i m j (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (n + 1 + (m + 1)))} (Finset.singleton_nonempty _)
          (simplexHADecodePrefix_cut (n + 1 + m) v))
        (simplexHABeadWordRawValue A s
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (n + 1 + (m + 1)))) hb)) (by
            simp only [Finset.card_singleton, Nat.add_sub_cancel, Nat.cast_add]
            omega)) := by
  let p := serreCubeGeneratorFreeDimension n i
  let q := serreCubeGeneratorFreeDimension m j
  let vp := Fin.castSuccOrderEmb.trans v
  let r := v (Fin.last (n + 1 + (m + 1)))
  let L := simplexHABeadWordRawValue A s
    (simplexHAGeneratorWord n i (simplexHASplitLeft n (m + 1) v)
      (simplexHASplitCut n (m + 1) v) (simplexHASplitLeft_last_lt n (m + 1) v))
  let R := simplexHABeadWordRawValue A s
    (simplexHAGeneratorWord m j (simplexHASplitRight n m vp) r
      (simplexHADecodePrefix_last m (simplexHASplitRight n (m + 1) v)))
  let Q := simplexHABeadWordRawValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb)
  have hp := Finset.card_pos.mpr hT
  have hR := simplexHABeadWordDecode_one_rawValue A s m j (simplexHASplitRight n (m + 1) v)
    T hT (fun r hr => lt_of_eq_of_lt (simplexHASplitRight_last n (m + 1) v) (hb r hr))
  have hs : -(q : ℤ) + -((T.card - 1 : ℕ) : ℤ) = -((q + (T.card - 1) : ℕ) : ℤ) := by omega
  have h₀ : HEq (simplexHASplitRawValue A s n i (m + 1) (j, 1) v T hT hb)
      (forward A (n := -((p + q + T.card - 1 : ℕ) : ℤ)) L (forward A R Q hs) (by omega)) := by
    exact dgForward_heq A rfl rfl rfl rfl (by
      change -((q + T.card - 1 : ℕ) : ℤ) = -((q + (T.card - 1) : ℕ) : ℤ)
      omega) rfl _ _ _ _ _ _ HEq.rfl hR
  have h₁ := dgForward_assoc_heq A L R Q
    (show -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ) by omega) hs
    (show -((p + q : ℕ) : ℤ) + -((T.card - 1 : ℕ) : ℤ) =
      -((p + q + (T.card - 1) : ℕ) : ℤ) by omega)
    (show -(p : ℤ) + -((q + (T.card - 1) : ℕ) : ℤ) =
      -((p + q + T.card - 1 : ℕ) : ℤ) by omega)
  exact h₀.trans h₁.symm

/-- 元の右ブロックの辺は、同じ最右頂点を右側集合に加えた左右合成値。 -/
lemma simplexHASplitRawValue_edge :
    HEq (simplexHASplitRawValue A s n i (m + 1) (j, 2) v T hT hb)
      (simplexHASplitRawValue A s n i m j (Fin.castSuccOrderEmb.trans v)
        (insert (v (Fin.last (n + 1 + (m + 1)))) T) (Finset.insert_nonempty _ T)
        (simplexHADecodePrefix_insert (n + 1 + m) v T hb)) := by
  have hc := Finset.card_insert_of_notMem
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (n + 1 + (m + 1)))) hb)
  have hR := simplexHABeadWordDecode_edge_rawValue A s m j (simplexHASplitRight n (m + 1) v)
    T hT (fun r hr => lt_of_eq_of_lt (simplexHASplitRight_last n (m + 1) v) (hb r hr))
  unfold simplexHASplitRawValue
  exact dgForward_heq A rfl rfl (by
    exact congrArg s.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb).symm) rfl
    (by change -((serreCubeGeneratorFreeDimension m j + 1 + T.card - 1 : ℕ) : ℤ) = _
        rw [hc]; omega)
    (by change -((serreCubeGeneratorFreeDimension n i +
          (serreCubeGeneratorFreeDimension m j + 1) + T.card - 1 : ℕ) : ℤ) = _
        rw [hc]; omega) _ _ _ _ _ _ HEq.rfl hR

end SerrePositivity.KST.SConstruction
