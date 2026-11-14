module
public import SerrePositivity.KST.SConstruction.SimplexHADeleteVertexOrder
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorIndex
public import SerrePositivity.KST.SConstruction.SimplexHADecodeRightTail
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexHABeadWordJoinEquality

/-! # 元の全生成元への任意座標の零端点挿入の読み替え
概要：任意位置の零端点を挿入した語を、同じ内部頂点を削除した語として回収する。
方針：元の最右因子の零・一・辺の三再帰と、削除列の前段・最右頂点の一致を使う。
規約：右側集合の内部自由座標を保持。使われ方：任意座標の実零面への復元の制限。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

private lemma tail_start_heq {n : ℕ} (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    {a a' : Fin (n + 1)} (ha : a = a') (hb : ∀ r ∈ T, a < r)
    (hb' : ∀ r ∈ T, a' < r) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT a hb) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT a' hb') := by
  cases ha
  rfl

/-- 元の右端への零端点挿入は、同じ最右内部頂点を削除した元の語。 -/
lemma simplexHABeadWordDecode_insert_zero_right {n : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last (m + 1)) < r) :
    HEq (simplexHABeadWordDecode (m + 1) (serreCubeInsertGeneratorIndex false m 0 i) v T hT hb)
      (simplexHABeadWordDecode m i (simplexHADeleteVertexOrder m 0 v) T hT
        (simplexHADeleteVertexOrder_bound m 0 v T hb)) := by
  have h := simplexHABeadWordDecode_zero m i v T hT hb
  have h' := simplexHABeadWordDecode_congr_heq m i (Fin.castSuccOrderEmb.trans v)
    (simplexHADeleteVertexOrder m 0 v) (simplexHADeleteVertexOrder_zero m v).symm
    T T rfl hT hT (simplexHADecodePrefix_tail m v T hb)
    (simplexHADeleteVertexOrder_bound m 0 v T hb)
  rw [serreCubeInsertGeneratorIndex_zero]
  exact (heq_of_eq h).trans h'

/-- 元の全座標への零端点挿入は、元の同じ内部頂点だけを削除した読み替え語。 -/
lemma simplexHABeadWordDecode_insert_zero {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last (m + 1)) < r) :
    HEq (simplexHABeadWordDecode (m + 1) (serreCubeInsertGeneratorIndex false m q i) v T hT hb)
      (simplexHABeadWordDecode m i (simplexHADeleteVertexOrder m q v) T hT
        (simplexHADeleteVertexOrder_bound m q v T hb)) := by
  induction m generalizing T with
  | zero =>
    have hq : q = 0 := Fin.ext (by have hq := q.isLt; omega)
    subst q
    exact simplexHABeadWordDecode_insert_zero_right 0 i v T hT hb
  | succ m ih =>
    refine Fin.cases (simplexHABeadWordDecode_insert_zero_right (m + 1) i v T hT hb)
      (fun q => ?_) q
    obtain ⟨i, j⟩ := i
    let u := simplexHADeleteVertexOrder (m + 1) q.succ v
    have hu := simplexHADeleteVertexOrder_bound (m + 1) q.succ v T hb
    have hp : simplexHADeleteVertexOrder m q (Fin.castSuccOrderEmb.trans v) =
        Fin.castSuccOrderEmb.trans u :=
      (simplexHADeleteVertexOrder_succ_prefix m q v).symm
    have hr : u (Fin.last (m + 1)) = v (Fin.last (m + 2)) :=
      simplexHADeleteVertexOrder_succ_last m q v
    have hf : u 0 = v 0 := simplexHADeleteVertexOrder_first (m + 1) q.succ v
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) j
    · have h₀ := simplexHABeadWordDecode_zero (m + 1)
        (serreCubeInsertGeneratorIndex false m q i) v T hT hb
      have h₁ := ih q i (Fin.castSuccOrderEmb.trans v) T hT
        (simplexHADecodePrefix_tail (m + 1) v T hb)
      have h₂ := simplexHABeadWordDecode_congr_heq m i _ _ hp T T rfl hT hT
        (simplexHADeleteVertexOrder_bound m q (Fin.castSuccOrderEmb.trans v) T
          (simplexHADecodePrefix_tail (m + 1) v T hb))
        (simplexHADecodePrefix_tail m u T hu)
      have h₃ := simplexHABeadWordDecode_zero m i u T hT hu
      exact (heq_of_eq h₀).trans (h₁.trans (h₂.trans (heq_of_eq h₃).symm))
    · let r := v (Fin.last (m + 2))
      let r' := u (Fin.last (m + 1))
      have h₀ := simplexHABeadWordDecode_one (m + 1)
        (serreCubeInsertGeneratorIndex false m q i) v T hT hb
      have h₁ := ih q i (Fin.castSuccOrderEmb.trans v) {r} (Finset.singleton_nonempty r)
        (simplexHADecodePrefix_cut (m + 1) v)
      have h₂ := simplexHABeadWordDecode_congr_heq m i _ _ hp {r} {r'}
        (congrArg (fun x => ({x} : Finset (Fin (n + 1)))) hr.symm)
        (Finset.singleton_nonempty r) (Finset.singleton_nonempty r')
        (simplexHADeleteVertexOrder_bound m q (Fin.castSuccOrderEmb.trans v) {r}
          (simplexHADecodePrefix_cut (m + 1) v)) (simplexHADecodePrefix_cut m u)
      have htail := tail_start_heq T hT hr.symm hb hu
      have hj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordJoin_heq hf.symm hr.symm rfl
        (serreCubeInsertGeneratorIndex_freeDimension false m q i) rfl _ _ _ _
        (h₁.trans h₂) htail
      have h₃ := simplexHABeadWordDecode_one m i u T hT hu
      exact h₀.trans (hj.trans h₃.symm)
    · have h₀ := simplexHABeadWordDecode_edge (m + 1)
        (serreCubeInsertGeneratorIndex false m q i) v T hT hb
      have h₁ := ih q i (Fin.castSuccOrderEmb.trans v)
        (insert (v (Fin.last (m + 2))) T) (Finset.insert_nonempty _ T)
        (simplexHADecodePrefix_insert (m + 1) v T hb)
      have h₂ := simplexHABeadWordDecode_congr_heq m i _ _ hp _ _
        (congrArg (fun x => insert x T) hr.symm)
        (Finset.insert_nonempty _ T) (Finset.insert_nonempty _ T)
        (simplexHADeleteVertexOrder_bound m q (Fin.castSuccOrderEmb.trans v) _
          (simplexHADecodePrefix_insert (m + 1) v T hb))
        (simplexHADecodePrefix_insert m u T hu)
      have h₃ := simplexHABeadWordDecode_edge m i u T hT hu
      exact h₀.trans (h₁.trans (h₂.trans h₃.symm))

end SerrePositivity.KST.SConstruction
