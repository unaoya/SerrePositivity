module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceEraseSubset
public import SerrePositivity.KST.SConstruction.SerreCubeFaceGeneratorIndex
public import SerrePositivity.KST.SConstruction.SimplexHATopDecodeValue

/-! # 元の零面一端点読み替えと HA 削除成分
概要：指定座標だけを零端点とする語の値を、同じ内部頂点を削除した HA 成分へ戻す。
方針：元の右端での削除と内側への辺保持を、同じ削除部分集合の等号で帰納する。
規約：任意の HA データと右側集合を保持。使われ方：元の全面零面像の HA 評価。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の面座標の内部頂点を削除した、同じ端点・自由次数の HA 成分。 -/
def simplexHADeletedFaceValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1)) :
    GradedHom A (s.obj (v 0)) (s.obj (T.max' hT)) (-((m + T.card - 1 : ℕ) : ℤ)) :=
  s.hom ((simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m i)))
    (v 0) (T.max' hT) _ (simplexHAFaceErase_two m v T hT hb i)
    (simplexHAFaceErase_min m v T hT hb i) (simplexHAFaceErase_max m v T hT hb i) (by
      have hc := simplexHAFaceErase_card m v T hb i
      have hp := Finset.card_pos.mpr hT
      omega)

/-- 元の右端零面添字の語の値は、前段の元の全辺読み替えの値。 -/
lemma simplexHABeadWordDecode_face_zero_right {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (simplexHABeadWordValue A s
      (simplexHABeadWordDecode (m + 1) (serreCubeFaceGeneratorIndex false m 0) v T hT hb))
      (simplexHABeadWordValue A s (simplexHABeadWordDecode m (serreCubeTopGeneratorIndex m)
        (Fin.castSuccOrderEmb.trans v) T hT (simplexHADecodePrefix_tail m v T hb))) := by
  cases m <;> rfl

/-- 元の全零面の一端点語の評価は、同じ内部頂点を削除した元の HA 成分。 -/
lemma simplexHABeadWordDecode_face_zero_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1)) :
    HEq (simplexHABeadWordValue A s
      (simplexHABeadWordDecode (m + 1) (serreCubeFaceGeneratorIndex false m i) v T hT hb))
      (simplexHADeletedFaceValue A s m v T hT hb i) := by
  have hz (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
      (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
      HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1)
        (serreCubeFaceGeneratorIndex false m 0) v T hT hb))
        (simplexHADeletedFaceValue A s m v T hT hb 0) := by
    have he : simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) T =
        (simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m 0)) := by
      rw [simplexHAFaceVertex_zero, simplexHADecodeSubset_erase m v T hb]
    exact (simplexHABeadWordDecode_face_zero_right A s m v T hT hb).trans
      ((simplexHABeadWordDecode_top_value A s m (Fin.castSuccOrderEmb.trans v)
        T hT (simplexHADecodePrefix_tail m v T hb)).trans
          (s.hom_heq_of_indices_degree he rfl rfl rfl))
  induction m generalizing T with
  | zero =>
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; omega)
    subst i
    exact hz 0 v T hT hb
  | succ m ih =>
    refine Fin.cases (hz (m + 1) v T hT hb) (fun j => ?_) i
    let r := v (Fin.last (m + 2))
    have he :
        (simplexHADecodeSubset (m + 1) (Fin.castSuccOrderEmb.trans v) (insert r T)).erase
          ((Fin.castSuccOrderEmb.trans v) (simplexHAFaceVertex m j)) =
        (simplexHADecodeSubset (m + 2) v T).erase
          (v (simplexHAFaceVertex (m + 1) j.succ)) := by
      rw [simplexHADecodeSubset_insert_tail, simplexHAFaceVertex_succ]
      rfl
    have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb)
    exact (simplexHABeadWordDecode_edge_value A s (m + 1)
      (serreCubeFaceGeneratorIndex false m j) v T hT hb).trans
      ((ih (Fin.castSuccOrderEmb.trans v) (insert r T) (Finset.insert_nonempty r T)
        (simplexHADecodePrefix_insert (m + 1) v T hb) j).trans
          (s.hom_heq_of_indices_degree he rfl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb) (by omega)))

end SerrePositivity.KST.SConstruction
