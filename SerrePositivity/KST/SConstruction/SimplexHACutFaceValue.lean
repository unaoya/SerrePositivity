module
public import SerrePositivity.KST.SConstruction.SimplexHADeletedFaceValue
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetFilters
public import SerrePositivity.KST.SConstruction.DGComposeHeterogeneous

/-! # 元の一面一端点読み替えと HA 切断合成
概要：指定座標だけを一端点とする語の値を、同じ内部頂点での HA 切断合成へ戻す。
方針：右端の全辺と右側 bead の評価を両フィルターへ移し、辺保持で帰納する。
規約：任意の HA データ・元の通常順合成を保持。使われ方：元の全面一面像の評価。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の面座標の内部頂点での、元の同じ部分集合・端点の HA 切断合成。 -/
def simplexHACutFaceValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1)) :
    GradedHom A (s.obj (v 0)) (s.obj (T.max' hT)) (-((m + T.card : ℕ) : ℤ) + 1) :=
  s.cutComposite (simplexHADecodeSubset (m + 1) v T) (v 0) (T.max' hT) _
    (simplexHADecodeSubset_two (m + 1) v T hT hb)
    (simplexHADecodeSubset_min (m + 1) v T hb).symm
    (simplexHADecodeSubset_max (m + 1) v T hT hb).symm (by
      have hc := simplexHADecodeSubset_card (m + 1) v T hb
      omega) (v (simplexHAFaceVertex m i)) (simplexHAFaceVertex_mem m v T i)
      (simplexHAFaceVertex_first_lt m v i)
      (simplexHAFaceVertex_tail_lt m v T i hb _ (Finset.max'_mem T hT))

/-- 元の右端一面の一端点語の評価は、同じ最右頂点での元の HA 切断合成。 -/
lemma simplexHABeadWordDecode_face_one_right {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
      (serreCubeFaceGeneratorIndex true m 0) v T hT hb))
      (simplexHACutFaceValue A s m v T hT hb 0) := by
  let I := simplexHADecodeSubset (m + 1) v T
  let r := v (Fin.last (m + 1))
  have hI := simplexHADecodeSubset_two (m + 1) v T hT hb
  have ha := (simplexHADecodeSubset_min (m + 1) v T hb).symm
  have hM := (simplexHADecodeSubset_max (m + 1) v T hT hb).symm
  have hr := simplexHADecodeSubset_cut_mem m v T
  let left := s.cutLeft I (v 0) hI ha r hr (v.strictMono (by
    change (0 : ℕ) < m + 1
    omega))
  let right := s.cutRight I (T.max' hT) hI hM r hr (hb _ (Finset.max'_mem T hT))
  have hL := simplexHADecodeSubset_filter_left_decode m v T hb
  have hR := simplexHADecodeSubset_filter_right m v T hb
  have hcL := simplexHADecodeSubset_card m (Fin.castSuccOrderEmb.trans v) {r}
    (simplexHADecodePrefix_cut m v)
  have hcR := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb)
  dsimp only [r] at hcL hcR
  have hp := Finset.card_pos.mpr hT
  have hd := serreCubeTopGeneratorIndex_freeDimension m
  have hl : HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode m
      (serreCubeTopGeneratorIndex m) (Fin.castSuccOrderEmb.trans v) {r}
      (Finset.singleton_nonempty r) (simplexHADecodePrefix_cut m v))) left :=
    (simplexHABeadWordDecode_top_value A s m (Fin.castSuccOrderEmb.trans v) {r}
      (Finset.singleton_nonempty r) (simplexHADecodePrefix_cut m v)).trans
        (s.hom_heq_of_indices_degree hL.symm rfl rfl (by
          simp only [Finset.card_singleton] at hcL ⊢
          rw [hL]
          omega))
  have hri : 2 ≤ (insert r T).card := by
    dsimp only [r]
    omega
  have hmin : r = (insert r T).min' (Finset.insert_nonempty r T) := by
    symm
    apply (Finset.min'_eq_iff _ _ _).mpr
    constructor
    · exact Finset.mem_insert_self r T
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hb x hx).le
  have hmax : T.max' hT = (insert r T).max' (Finset.insert_nonempty r T) :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb).symm
  have hright : HEq (simplexHABeadWordValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb)) right :=
    (heq_of_eq (simplexHABeadTail_value A s T hT r hb hri hmin hmax)).trans
      (s.hom_heq_of_indices_degree hR.symm rfl rfl (by rw [hR]; omega))
  have hzero : HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
      (serreCubeFaceGeneratorIndex true m 0) v T hT hb))
      (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
        (serreCubeTopGeneratorIndex m, 1) v T hT hb)) := by cases m <;> rfl
  have hf : v 0 < r := v.strictMono (by change (0 : ℕ) < m + 1; omega)
  have hk : -((m + T.card : ℕ) : ℤ) = 2 - (I.card : ℤ) := by
    have hc := simplexHADecodeSubset_card (m + 1) v T hb
    dsimp only [I]
    omega
  have hcut : HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
      (serreCubeFaceGeneratorIndex true m 0) v T hT hb))
      (s.cutComposite I (v 0) (T.max' hT) (-((m + T.card : ℕ) : ℤ)) hI ha hM hk
        r hr hf (hb _ (Finset.max'_mem T hT))) := by
    exact hzero.trans ((simplexHABeadWordDecode_one_value A s m
      (serreCubeTopGeneratorIndex m) v T hT hb).trans
        (dgCompose_heq A (by
          change -(serreCubeGeneratorFreeDimension m (serreCubeTopGeneratorIndex m) : ℤ) = _
          rw [hd, hL]
          simp only [Finset.card_singleton] at hcL
          omega) (by
            rw [hR]
            omega) (by omega) _ _ left right _ _ hl hright))
  exact hcut.trans (simplexHACutComposite_heq A s rfl rfl rfl rfl
    (congrArg v (simplexHAFaceVertex_zero m).symm))

/-- 元の全一面の一端点語の評価は、同じ内部頂点での元の HA 切断合成。 -/
lemma simplexHABeadWordDecode_face_one_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1)) :
    HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
      (serreCubeFaceGeneratorIndex true m i) v T hT hb))
      (simplexHACutFaceValue A s m v T hT hb i) := by
  induction m generalizing T with
  | zero =>
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; omega)
    subst i
    exact simplexHABeadWordDecode_face_one_right A s 0 v T hT hb
  | succ m ih =>
    refine Fin.cases (simplexHABeadWordDecode_face_one_right A s (m + 1) v T hT hb)
      (fun j => ?_) i
    let r := v (Fin.last (m + 2))
    have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb)
    have hj : (Fin.castSuccOrderEmb.trans v) (simplexHAFaceVertex m j) =
        v (simplexHAFaceVertex (m + 1) j.succ) := by rw [simplexHAFaceVertex_succ]; rfl
    exact (simplexHABeadWordDecode_edge_value A s (m + 1)
      (serreCubeFaceGeneratorIndex true m j) v T hT hb).trans
      ((ih (Fin.castSuccOrderEmb.trans v) (insert r T) (Finset.insert_nonempty r T)
        (simplexHADecodePrefix_insert (m + 1) v T hb) j).trans
          (simplexHACutComposite_heq A s (simplexHADecodeSubset_insert_tail (m + 1) v T)
            rfl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb) (by omega) hj))

end SerrePositivity.KST.SConstruction
