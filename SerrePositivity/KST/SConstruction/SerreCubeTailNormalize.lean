module
public import SerrePositivity.KST.SConstruction.SerreCubeChainReindex
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetZeroFace

/-! # 元の右側自由座標の濃度表示への移送
概要：p+(|T|−1) 次元の元の鎖射を、読み替えに使う p+|T|−1 次元へ移す。
方針：非空な T の元の濃度から次元等号を作り、始域・終域の同じ移送を使う。
規約：元の自由座標と面座標を保持。使われ方：全生成元標準面と実部分集合の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の非空な右側集合の自由次元は、読み替えの元の濃度表示と一致する。 -/
lemma serreCubeTail_dimension {k : ℕ} (p : ℕ) (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    p + T.card - 1 = p + (T.card - 1) := by
  have hp := Finset.card_pos.mpr hT
  omega

variable (A : Type u) [CommRing A]

/-- 元の右側自由座標を持つ実鎖射の両次元を、読み替えの元の濃度表示へ移す。 -/
def serreCubeTailNormalize {k p q : ℕ} (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (f : serreCubeComplex A (p + (T.card - 1)) ⟶ serreCubeComplex A (q + (T.card - 1))) :
    serreCubeComplex A (p + T.card - 1) ⟶ serreCubeComplex A (q + T.card - 1) :=
  serreCubeChainReindex A (serreCubeTail_dimension p T hT)
    (serreCubeTail_dimension q T hT).symm f

/-- 元の濃度表示への移送前後で、元の同じ実鎖射と異種等号で一致する。 -/
lemma serreCubeTailNormalize_heq {k p q : ℕ} (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (f : serreCubeComplex A (p + (T.card - 1)) ⟶ serreCubeComplex A (q + (T.card - 1))) :
    HEq (serreCubeTailNormalize A T hT f) f :=
  serreCubeChainReindex_heq A (serreCubeTail_dimension p T hT)
    (serreCubeTail_dimension q T hT).symm f

/-- 元の濃度表示への移送は、元の恒等射を保つ。 -/
lemma serreCubeTailNormalize_id {k : ℕ} (p : ℕ) (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeTailNormalize A T hT (𝟙 (serreCubeComplex A (p + (T.card - 1)))) =
      𝟙 (serreCubeComplex A (p + T.card - 1)) :=
  serreCubeChainReindex_id A (serreCubeTail_dimension p T hT)

/-- 元の中間次元を同じ濃度表示へ移せば、元の射の合成を厳密に保つ。 -/
lemma serreCubeTailNormalize_comp {k p q r : ℕ} (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (f : serreCubeComplex A (p + (T.card - 1)) ⟶ serreCubeComplex A (q + (T.card - 1)))
    (g : serreCubeComplex A (q + (T.card - 1)) ⟶ serreCubeComplex A (r + (T.card - 1))) :
    serreCubeTailNormalize A T hT (f ≫ g) =
      serreCubeTailNormalize A T hT f ≫ serreCubeTailNormalize A T hT g :=
  serreCubeChainReindex_comp A (serreCubeTail_dimension p T hT)
    (serreCubeTail_dimension q T hT) (serreCubeTail_dimension r T hT) f g

/-- 元の座標 |T|−1 の両標準面は、元の同じ読み替え次元の面へ厳密に移る。 -/
lemma serreCubeTailNormalize_face {k : ℕ} (b : Bool) (p : ℕ)
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty) :
    serreCubeTailNormalize A T hT
      (serreCubeChainFace A b (p + (T.card - 1)) ((p + 1) + (T.card - 1)) (by omega)
        ⟨T.card - 1, by omega⟩) =
      serreCubeChainFace A b (p + T.card - 1) ((p + 1) + T.card - 1)
        (simplexHADecodeSubset_face_codimension p T hT) (simplexHADecodeFaceCoordinate p T hT) := by
  have h := serreCubeChainReindex_face A b (serreCubeTail_dimension p T hT)
    (serreCubeTail_dimension (p + 1) T hT) (by omega)
    (simplexHADecodeSubset_face_codimension p T hT) ⟨T.card - 1, by omega⟩
  exact h.trans (by congr 2)

end SerrePositivity.KST.SConstruction
