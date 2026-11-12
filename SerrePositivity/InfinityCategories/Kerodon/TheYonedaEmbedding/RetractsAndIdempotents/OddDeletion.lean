module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OddDeletionOrder
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStages

/-!
概要：元の奇数頂点を除いた交互列の面を、元の短い交互列へ全単体ごと因子化する。
方針：隣接する二つの Y を潰す順序射と、同じ元の吸収射を比較する。
規約：元の恒等・包含・射影・全ての正の長さの射を保持する。
使われ方：Ret の隣接段階の元の逆像境界の順方向。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の吸収射は、端点の元の等式による移送で同じ元の吸収射に戻る。 -/
lemma walkingAbsorbingHom_transport {P Q P' Q' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}}
    (hP : P = P') (hQ : Q = Q') :
    eqToHom hP ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom P' Q' ≫ eqToHom hQ.symm = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom P Q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.comp_walkingAbsorbingHom]

/-- 元の分裂対象の表示を保つと、同じ元の吸収射は恒等。 -/
lemma walkingAbsorbingHom_self_of_image (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) (h : P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom P P = 𝟙 P := by
  subst P
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom_image

/-- 元の交互列の始点が Y なら、同じ元の射は長さ零の場合も吸収射。 -/
lemma alternatingChainMap_absorbing_of_image {n : ℕ} (a b : Fin (n + 1))
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject.{u} a.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} a b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
  by_cases hab : a = b
  · subst b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap_self]
    exact (walkingAbsorbingHom_self_of_image _ ha).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right hab]

/-- 元の奇数頂点の面を元の短い標準単体へ送る順序射。 -/
def oddFaceCollapseMap {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    ⦋2 * m + 1⦌ ⟶ ⦋2 * m⦌ := SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj)

/-- 元の余面の対象と、元の潰した短い列の対象は同じ元の二対象。 -/
lemma alternatingObject_oddFace {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1)
    (a : Fin (2 * m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject.{u} (j.succAbove a).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj a).val := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse_parity]

/-- 元の奇数頂点の面は、元の短い交互列への同じ順序射で全ての射を保って因子化する。 -/
lemma oddFaceChain {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain.{u} (2 * (m + 1)) =
      (SimplexCategory.toCat.map (oddFaceCollapseMap j hj)).toFunctor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * m) := by
  change (Fin.succAboveOrderEmb j).monotone.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * (m + 1)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj).monotone.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * m)
  refine CategoryTheory.Functor.ext (alternatingObject_oddFace j hj) ?_
  intro a b f
  by_cases hab : a = b
  · subst b
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    subst f
    simp
  have hlt : a < b := lt_of_le_of_ne (leOfHom f) hab
  have hbig : j.succAbove a ≠ j.succAbove b := fun h ↦ hab (Fin.succAbove_right_injective h)
  have hbigMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} (j.succAbove a) (j.succAbove b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right hbig]
  have hsmallMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
    by_cases he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj b
    · exact alternatingChainMap_absorbing_of_image _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse_fiber_image j hj hlt he)
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right he]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap (j.succAbove a) (j.succAbove b) =
    eqToHom (alternatingObject_oddFace j hj a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oddFaceCollapse j hj b) ≫
        eqToHom (alternatingObject_oddFace j hj b).symm
  rw [hbigMap, hsmallMap]
  exact (walkingAbsorbingHom_transport (alternatingObject_oddFace j hj a)
    (alternatingObject_oddFace j hj b)).symm

/-- 元の奇数頂点の余面の全交互セルは、元の短い交互セルを厳密に経由する。 -/
lemma alternatingCell_oddFace {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} (m + 1) =
      SSet.stdSimplex.map (oddFaceCollapseMap j hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m := by
  change stdSimplex.δ j ≫
    (SSet.yonedaEquiv (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u})).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * m + 1 + 1)) =
      SSet.stdSimplex.map (oddFaceCollapseMap j hj) ≫
        (SSet.yonedaEquiv (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u})).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * m))
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg SSet.yonedaEquiv.symm (oddFaceChain j hj)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
