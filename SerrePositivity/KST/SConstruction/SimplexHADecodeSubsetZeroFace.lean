module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCell
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaSpecifiedFace

/-! # 元の読み替え次元の部分集合生成射の標準零面
概要：右側自由次元の座標の元の零面で、同じ削除済み左部分の実生成射を回収する。
方針：元の削除部分集合・次元・座標の同定を、指定次元の実零面定理へ適用する。
規約：元の標準零面と端点を保持。使われ方：全生成元読み替えの零端点帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の右側集合が非空なら、削除前後の読み替え次元は余次元一。 -/
lemma simplexHADecodeSubset_face_codimension {n : ℕ} (m : ℕ)
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) :
    (m + T.card - 1) + 1 = (m + 1) + T.card - 1 := by
  have hp := Finset.card_pos.mpr hT
  omega

/-- 元の標準両面に使う、同じ右側自由次元の数値座標。 -/
def simplexHADecodeFaceCoordinate {n : ℕ} (m : ℕ)
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) : Fin ((m + 1) + T.card - 1) :=
  ⟨T.card - 1, by have hp := Finset.card_pos.mpr hT; omega⟩

variable (A : Type u) [CommRing A]

/-- 元の読み替え次元の実生成射の零面は、同じ左部分・右側集合の実生成射。 -/
lemma simplexHADecodeSubsetCell_zero_face {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    serreCubeChainFace A false (m + T.card - 1) ((m + 1) + T.card - 1)
        (simplexHADecodeSubset_face_codimension m T hT) (simplexHADecodeFaceCoordinate m T hT) ≫
      simplexHADecodeSubsetCell A (m + 1) v T hT hb =
    simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v) T hT
      (simplexHADecodePrefix_tail m v T hb) := by
  let I := simplexHADecodeSubset (m + 1) v T
  let r := v (Fin.last (m + 1))
  have hI : 2 ≤ I.card := simplexHADecodeSubset_two (m + 1) v T hT hb
  have hj : r ∈ I := simplexHADecodeSubset_cut_mem m v T
  have hmin := simplexHADecodeSubset_cut_min m v T hb
  have hmax := simplexHADecodeSubset_cut_max m v T hT hb
  have hp : m + T.card - 1 = (I.erase r).card - 2 := by
    dsimp only [I, r]
    rw [simplexHADecodeSubset_erase m v T hb,
      simplexHADecodeSubset_dimension m (Fin.castSuccOrderEmb.trans v) T
        (simplexHADecodePrefix_tail m v T hb)]
  have hq : (m + 1) + T.card - 1 = I.card - 2 :=
    (simplexHADecodeSubset_dimension (m + 1) v T hb).symm
  have hi : Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI r hj hmin hmax) =
      simplexHADecodeFaceCoordinate m T hT := by
    apply Fin.ext
    exact simplexHADecodeSubset_erase_coordinate m v T hT hb hI
  have hz := simplexSubsetLambdaCellAtDimension_zero_face_at A I hI r hj hmin hmax
    (v 0) (T.max' hT) (simplexHADecodeSubset_min (m + 1) v T hb).symm
    (simplexHADecodeSubset_max (m + 1) v T hT hb).symm
    (m + T.card - 1) ((m + 1) + T.card - 1) hp hq
    (simplexHADecodeSubset_face_codimension m T hT)
  rw [hi] at hz
  unfold simplexHADecodeSubsetCell
  apply hz.trans
  apply simplexSubsetLambdaCellAtDimension_congr A _ _ (simplexHADecodeSubset_erase m v T hb)

end SerrePositivity.KST.SConstruction
