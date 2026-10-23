module

public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutStage
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseWeightReindexCoordinates

/-!
概要：混合 Hom の段階ごとの評価は、実際の edgewise 重みの面・退化と可換。
方針：path の像と座標の自然性を、左右の頂点の計算へ適用する。
規約：頂点番号だけでなく重みからの射そのものの可換性を記録する。
使われ方：coherent な二対象の単体の面・退化自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 単調な添字変換による path の像を、path 圏の間の関手へ束ねる。 -/
def pathCutImageFunctor {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (i j : Fin (m + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j) ⥤
      Path (ULift.up (α i) : ULift.{u} (Fin (n + 1))) (ULift.up (α j)) where
  obj P := pathCutImage α P
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 段階を含む混合座標は、実際の edgewise の添字変換で対応する座標へ写る。 -/
lemma pathCutEdgewiseStageCoordinate_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) {i j : Fin (m + 1)}
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    pathCutEdgewiseCoordinate t hi hj (pathCutImage α.toOrderHom P)
        (s (pathCutLastZero t hi (pathCutImage α.toOrderHom P))) =
      edgewiseWeightReindexOrderHom.{u} α
        (pathCutEdgewiseCoordinate (t.comp α.toOrderHom) hi hj P
          ((s.comp α.toOrderHom) (pathCutLastZero (t.comp α.toOrderHom) hi P))) := by
  simp only [pathCutEdgewiseCoordinate, pathCutLastZero_image, pathCutFirstOne_image,
    OrderHom.comp_coe, Function.comp_apply]
  split_ifs
  · exact (edgewiseWeightReindexOrderHom_left.{u} α _).symm
  · exact (edgewiseWeightReindexOrderHom_right.{u} α _).symm

/-- 段階の座標射は、path の像と元の重みの射の間の可換四角形を与える。 -/
lemma pathCutEdgewiseStageCoordinateMap_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1))
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1) :
    nerveMap (pathCutImageFunctor α.toOrderHom i j) ≫
      pathCutEdgewiseStageCoordinateMap t s hi hj =
    pathCutEdgewiseStageCoordinateMap (t.comp α.toOrderHom) (s.comp α.toOrderHom) hi hj ≫
      edgewiseWeightStandardMap.{u} α := by
  rw [← edgewiseWeightReindexOrderHom_map]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  exact pathCutEdgewiseStageCoordinate_image α t s hi hj (P.obj k)

/-- 元の Hom 単体を評価した作用も、面・退化の両方を厳密に保つ。 -/
lemma pathCutEdgewiseStageMap_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1))
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1)
    {H : SSet.{u}} (σ : (edgewiseSubdivision H) _⦋n⦌) :
    nerveMap (pathCutImageFunctor α.toOrderHom i j) ≫ pathCutEdgewiseStageMap t s hi hj σ =
      pathCutEdgewiseStageMap (t.comp α.toOrderHom) (s.comp α.toOrderHom) hi hj
        ((edgewiseSubdivision H).map α.op σ) := by
  rw [pathCutEdgewiseStageMap, pathCutEdgewiseStageMap, ← Category.assoc,
    pathCutEdgewiseStageCoordinateMap_image, Category.assoc]
  simp only [edgewiseWeightStandardMap, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end SerrePositivity.InfinityCategories
