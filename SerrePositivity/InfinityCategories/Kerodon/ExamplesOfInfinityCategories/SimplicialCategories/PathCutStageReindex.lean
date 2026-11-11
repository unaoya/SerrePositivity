module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutStage
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates

/-!
概要：混合 Hom の段階ごとの評価は、実際の edgewise 重みの面・退化と可換。
方針：path の像と座標の自然性を、左右の頂点の計算へ適用する。
規約：頂点番号だけでなく重みからの射そのものの可換性を記録する。
使われ方：coherent な二対象の単体の面・退化自然性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 単調な添字変換による path の像を、path 圏の間の関手へ束ねる。 -/
def pathCutImageFunctor {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (i j : Fin (m + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j) ⥤
      Path (ULift.up (α i) : ULift.{u} (Fin (n + 1))) (ULift.up (α j)) where
  obj P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutImage α P
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 段階を含む混合座標は、実際の edgewise の添字変換で対応する座標へ写る。 -/
lemma pathCutEdgewiseStageCoordinate_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) {i j : Fin (m + 1)}
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate t hi hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutImage α.toOrderHom P)
        (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutImage α.toOrderHom P))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} α
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate (t.comp α.toOrderHom) hi hj P
          ((s.comp α.toOrderHom) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (t.comp α.toOrderHom) hi P))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_image, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_image,
    OrderHom.comp_coe, Function.comp_apply]
  split_ifs
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_left.{u} α _).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_right.{u} α _).symm

/-- 段階の座標射は、path の像と元の重みの射の間の可換四角形を与える。 -/
lemma pathCutEdgewiseStageCoordinateMap_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1))
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1) :
    nerveMap (pathCutImageFunctor α.toOrderHom i j) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageCoordinateMap t s hi hj =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageCoordinateMap (t.comp α.toOrderHom) (s.comp α.toOrderHom) hi hj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightStandardMap.{u} α := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_map]
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
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    nerveMap (pathCutImageFunctor α.toOrderHom i j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap t s hi hj σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap (t.comp α.toOrderHom) (s.comp α.toOrderHom) hi hj
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H).map α.op σ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap, ← Category.assoc,
    pathCutEdgewiseStageCoordinateMap_image, Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightStandardMap, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
