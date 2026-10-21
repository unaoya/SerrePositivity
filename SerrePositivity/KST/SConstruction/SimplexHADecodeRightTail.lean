module
public import SerrePositivity.KST.SConstruction.SimplexHATailPrefix
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightIndex
public import SerrePositivity.KST.SConstruction.SimplexHADecodeEquations

/-! # 元の右側全辺付加と右側頂点集合の読み替え
概要：元の右側列を全辺添字として付加した語を、同じ右側集合を持つ語へ戻す。
方針：昇順列の最後から辺の再帰式を適用し、元の列と集合の等号で移送する。
規約：元の全自由座標を保持。使われ方：辺付加の微分像と HA 語境界の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の頂点列・右側集合の等号は、全端点・自由次元を保つ同じ語の異種等号を与える。 -/
lemma simplexHABeadWordDecode_congr_heq {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v v' : Fin (m + 1) ↪o Fin (n + 1)) (hv : v = v')
    (T T' : Finset (Fin (n + 1))) (hTT : T = T') (hT : T.Nonempty) (hT' : T'.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) (hb' : ∀ r ∈ T', v' (Fin.last m) < r) :
    HEq (simplexHABeadWordDecode m i v T hT hb)
      (simplexHABeadWordDecode m i v' T' hT' hb') := by
  cases hv
  cases hTT
  rfl

/-- 元の右側列の像と上界以右の集合との和は、元の前段列の最後より右にある。 -/
lemma simplexHATailUnion_bound {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (t : ℕ) (w : Fin t ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b : Fin (n + 1)) (hv : v (Fin.last m) < b)
    (T : Finset (Fin (n + 1))) (hT : ∀ r ∈ T, b ≤ r) :
    ∀ r ∈ Finset.univ.map w.toEmbedding ∪ T, v (Fin.last m) < r := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hr
    exact hs j
  · exact hv.trans_le (hT r hr)

/-- 元の全辺付加で連結した列の語は、元の右側集合を保つ読み替えと一致する。 -/
lemma simplexHABeadWordDecode_rightTail {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (n + 1))
    (t : ℕ) (w : Fin t ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b : Fin (n + 1)) (hv : v (Fin.last m) < b) (hw : ∀ j, w j < b)
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (hTb : ∀ r ∈ T, b ≤ r) :
    HEq (simplexHABeadWordDecode (m + t) (serreCubeGeneratorRightIndex m i t)
      (simplexHATailPrefix m v t w hs b hv hw).val T hT
      (fun r hr => (simplexHATailPrefix m v t w hs b hv hw).property.trans_le (hTb r hr)))
      (simplexHABeadWordDecode m i v (Finset.univ.map w.toEmbedding ∪ T)
        (hT.mono Finset.subset_union_right) (simplexHATailUnion_bound m v t w hs b hv T hTb)) := by
  induction t generalizing b T with
  | zero =>
    exact simplexHABeadWordDecode_congr_heq m i v v rfl T _
      (by simp only [Finset.univ_eq_empty, Finset.map_empty, Finset.empty_union]) _ _ _ _
  | succ t ih =>
    let r := w (Fin.last t)
    let wp := Fin.castSuccOrderEmb.trans w
    let hs' : ∀ j, v (Fin.last m) < wp j := fun j => hs j.castSucc
    let hw' : ∀ j, wp j < r := fun j => w.strictMono (Fin.castSucc_lt_last j)
    let u := simplexHATailPrefix m v t wp hs' r (hs (Fin.last t)) hw'
    let v' := simplexHAOrderAppendLast (m + t) u.val r u.property
    have hb' : ∀ x ∈ T, v' (Fin.last (m + t + 1)) < x := fun x hx =>
      lt_of_eq_of_lt (simplexHAOrderAppendLast_last _ _ _ _) ((hw (Fin.last t)).trans_le
        (hTb x hx))
    have hrT : ∀ x ∈ insert r T, r ≤ x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hw (Fin.last t)).le.trans (hTb x hx)
    have huT : ∀ x ∈ insert r T, u.val (Fin.last (m + t)) < x :=
      fun x hx => u.property.trans_le (hrT x hx)
    have h₁ := simplexHABeadWordDecode_edge (m + t)
      (serreCubeGeneratorRightIndex m i t) v' T hT hb'
    have h₂ := simplexHABeadWordDecode_congr_heq (m + t)
      (serreCubeGeneratorRightIndex m i t) (Fin.castSuccOrderEmb.trans v') u.val
      (simplexHAOrderAppendLast_prefix _ _ _ _) _ (insert r T)
      (congrArg (fun x => insert x T) (simplexHAOrderAppendLast_last _ _ _ _))
      (Finset.insert_nonempty _ T) (Finset.insert_nonempty r T)
      (simplexHADecodePrefix_insert (m + t) v' T hb') huT
    have h₃ := ih wp hs' r (hs (Fin.last t)) hw' (insert r T)
      (Finset.insert_nonempty r T) hrT
    have hset : Finset.univ.map wp.toEmbedding ∪ insert r T =
        Finset.univ.map w.toEmbedding ∪ T := by
      rw [simplexHAOrderRange_succ w]
      simp only [Finset.union_insert, Finset.insert_union]
      rfl
    have h₄ := simplexHABeadWordDecode_congr_heq m i v v rfl _ _ hset
      ((Finset.insert_nonempty r T).mono Finset.subset_union_right)
      (hT.mono Finset.subset_union_right)
      (simplexHATailUnion_bound m v t wp hs' r (hs (Fin.last t)) (insert r T) hrT)
      (simplexHATailUnion_bound m v (t + 1) w hs b hv T hTb)
    exact h₁.trans (h₂.trans (h₃.trans h₄))

end SerrePositivity.KST.SConstruction
