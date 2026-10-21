module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightFaceChain
public import SerrePositivity.KST.SConstruction.SerreCubeTailNormalize

/-! # 元の全生成元標準面の読み替え次元への移送
概要：元の右側自由座標付き標準面の始域・終域を、同じ元の濃度表示へ揃える。
方針：元の両次元移送を使い、零・一端点と辺保持の実再帰を移す。
規約：元の標準面と数値座標を保持。使われ方：実部分集合生成射と全生成元語の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全生成元の標準面を、元の読み替えの始域・終域次元へ移す。 -/
def serreCubeGeneratorDecodeFace {k : ℕ} (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeComplex A (serreCubeGeneratorFreeDimension n i + T.card - 1) ⟶
      serreCubeComplex A (n + T.card - 1) :=
  serreCubeTailNormalize A T hT (serreCubeGeneratorRightFace A n i (T.card - 1)).hom

/-- 元の読み替え次元へ移した標準面は、同じ元の右側自由座標付き標準面と比較できる。 -/
lemma serreCubeGeneratorDecodeFace_heq {k : ℕ} (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    HEq (serreCubeGeneratorDecodeFace A n i T hT)
      (serreCubeGeneratorRightFace A n i (T.card - 1)).hom :=
  serreCubeTailNormalize_heq A T hT _

/-- 元の左生成元が零次元なら、元の読み替え次元の同じ恒等射。 -/
lemma serreCubeGeneratorDecodeFace_zero_left {k : ℕ} (i : SerreCubeGeneratorIndex 0)
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeGeneratorDecodeFace A 0 i T hT = 𝟙 (serreCubeComplex A (0 + T.card - 1)) := by
  unfold serreCubeGeneratorDecodeFace
  have h := congrArg (fun f => f.hom) (serreCubeGeneratorRightFace_zero_left A i (T.card - 1))
  rw [h]
  exact serreCubeTailNormalize_id A 0 T hT

/-- 元の右側集合が一点なら、元の同じ全生成元標準面を厳密に回収する。 -/
lemma serreCubeGeneratorDecodeFace_singleton {k : ℕ} (n : ℕ)
    (i : SerreCubeGeneratorIndex n) (b : Fin (k + 1)) :
    serreCubeGeneratorDecodeFace A n i {b} (Finset.singleton_nonempty b) =
      (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom := by
  unfold serreCubeGeneratorDecodeFace serreCubeTailNormalize serreCubeChainReindex
  change (𝟙 (serreCubeComplex A (serreCubeGeneratorFreeDimension n i))) ≫
    (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ≫
      𝟙 (serreCubeComplex A n) = _
  rw [Category.id_comp, Category.comp_id]

/-- 元の零端点追加は、読み替え次元の同じ座標の零面との実合成。 -/
lemma serreCubeGeneratorDecodeFace_point_zero {k : ℕ} (n : ℕ)
    (i : SerreCubeGeneratorIndex n) (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeGeneratorDecodeFace A (n + 1) (i, 0) T hT =
      serreCubeGeneratorDecodeFace A n i T hT ≫
        serreCubeChainFace A false (n + T.card - 1) ((n + 1) + T.card - 1)
          (simplexHADecodeSubset_face_codimension n T hT)
          (simplexHADecodeFaceCoordinate n T hT) := by
  let face := serreCubeChainFace A false (n + (T.card - 1)) ((n + 1) + (T.card - 1))
    (by omega) ⟨T.card - 1, by omega⟩
  have h := serreCubeGeneratorRightFace_point_zero_hom A n i (T.card - 1)
  have hm := congrArg (fun f : serreCubeComplex A
      (serreCubeGeneratorFreeDimension n i + (T.card - 1)) ⟶
        serreCubeComplex A ((n + 1) + (T.card - 1)) =>
      serreCubeTailNormalize A (p := serreCubeGeneratorFreeDimension n i) (q := n + 1) T hT f) h
  exact hm.trans ((serreCubeTailNormalize_comp A T hT
    (serreCubeGeneratorRightFace A n i (T.card - 1)).hom face).trans
      (congrArg (fun g => serreCubeTailNormalize A T hT
        (serreCubeGeneratorRightFace A n i (T.card - 1)).hom ≫ g)
        (serreCubeTailNormalize_face A false n T hT)))

/-- 元の一端点追加は、読み替え次元の同じ座標の一面との実合成。 -/
lemma serreCubeGeneratorDecodeFace_point_one {k : ℕ} (n : ℕ)
    (i : SerreCubeGeneratorIndex n) (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeGeneratorDecodeFace A (n + 1) (i, 1) T hT =
      serreCubeGeneratorDecodeFace A n i T hT ≫
        serreCubeChainFace A true (n + T.card - 1) ((n + 1) + T.card - 1)
          (simplexHADecodeSubset_face_codimension n T hT)
          (simplexHADecodeFaceCoordinate n T hT) := by
  let face := serreCubeChainFace A true (n + (T.card - 1)) ((n + 1) + (T.card - 1))
    (by omega) ⟨T.card - 1, by omega⟩
  have h := serreCubeGeneratorRightFace_point_one_hom A n i (T.card - 1)
  have hm := congrArg (fun f : serreCubeComplex A
      (serreCubeGeneratorFreeDimension n i + (T.card - 1)) ⟶
        serreCubeComplex A ((n + 1) + (T.card - 1)) =>
      serreCubeTailNormalize A (p := serreCubeGeneratorFreeDimension n i) (q := n + 1) T hT f) h
  exact hm.trans ((serreCubeTailNormalize_comp A T hT
    (serreCubeGeneratorRightFace A n i (T.card - 1)).hom face).trans
      (congrArg (fun g => serreCubeTailNormalize A T hT
        (serreCubeGeneratorRightFace A n i (T.card - 1)).hom ≫ g)
        (serreCubeTailNormalize_face A true n T hT)))

/-- 元の右側自由座標数の等号は、元の標準面の実鎖射の異種等号を与える。 -/
lemma serreCubeGeneratorRightFace_tail_heq (n : ℕ) (i : SerreCubeGeneratorIndex n)
    {t s : ℕ} (h : t = s) :
    HEq (serreCubeGeneratorRightFace A n i t).hom (serreCubeGeneratorRightFace A n i s).hom := by
  cases h
  rfl

/-- 元の辺追加は、同じ新頂点を右側集合へ移した標準面に異種等号で一致する。 -/
lemma serreCubeGeneratorDecodeFace_edge {k : ℕ} (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty) (r : Fin (k + 1)) (hr : r ∉ T) :
    HEq (serreCubeGeneratorDecodeFace A (n + 1) (i, 2) T hT)
      (serreCubeGeneratorDecodeFace A n i (insert r T) (Finset.insert_nonempty r T)) := by
  have ht : (T.card - 1) + 1 = (insert r T).card - 1 := by
    have hc := Finset.card_insert_of_notMem hr
    have hp := Finset.card_pos.mpr hT
    omega
  exact (serreCubeGeneratorDecodeFace_heq A (n + 1) (i, 2) T hT).trans
    ((serreCubeGeneratorRightFace_edge_hom A n i (T.card - 1)).trans
      ((serreCubeGeneratorRightFace_tail_heq A n i ht).trans
        (serreCubeGeneratorDecodeFace_heq A n i (insert r T) (Finset.insert_nonempty r T)).symm))

end SerrePositivity.KST.SConstruction
