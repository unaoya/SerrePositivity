module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates

/-!
概要：元の辺に付随する twisted arrow の二つの恒等点からの辺の座標。
方針：標準三単体の頂点列を明示し、edgewise 重みの二つの面を計算する。
規約：元の辺へ後合成する前の普遍的な標準単体で厳密に照合する。
使われ方：Yoneda の脚の恒等点像と反変側の恒等点輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 始点の恒等射から元の辺への Tw 辺に対応する頂点列 [0,0,0,1]。 -/
def twistedArrowSourceEdgeOrderHom : Fin 4 →o Fin 2 where
  toFun i := if i < 3 then 0 else 1
  monotone' := by intro i j hij; dsimp only; split_ifs <;> omega

/-- 終点の恒等射から元の辺への Tw 辺に対応する頂点列 [0,1,1,1]。 -/
def twistedArrowTargetEdgeOrderHom : Fin 4 →o Fin 2 where
  toFun i := if i = 0 then 0 else 1
  monotone' := by intro i j hij; dsimp only; split_ifs <;> omega

/-- 標準座標での合成式を、元の edgewise 重みの厳密な合成式へ戻す。 -/
lemma edgewiseWeight_reindex_comp_map {m n k : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (θ : Fin (n + n + 1 + 1) →o Fin (k + 1))
    (φ : Fin (m + m + 1 + 1) →o Fin (k + 1))
    (h : ∀ i, θ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} α i) = φ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map α ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} n).hom ≫
        stdSimplex.map (SimplexCategory.mkHom θ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} m).hom ≫ stdSimplex.map (SimplexCategory.mkHom φ) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} m).inv).mp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightStandardMap.{u} α ≫ stdSimplex.map (SimplexCategory.mkHom θ) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_map]
  have he : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} α) ≫
      SimplexCategory.mkHom θ = SimplexCategory.mkHom φ := by
    ext i
    exact congrArg Fin.val (h i)
  rw [← Functor.map_comp]
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    congrArg (fun f : ⦋m + m + 1⦌ ⟶ ⦋k⦌ ↦ stdSimplex.map f) he

/-- 二つの端点をともに指定頂点へ写す標準単体の順序写像。 -/
def twistedArrowConstantEdgeOrderHom (i : Fin 2) : Fin 2 →o Fin 2 :=
  OrderHom.const _ i

/-- 始点側 Tw 辺の先頭面は、始点の恒等射。 -/
lemma twistedArrowSourceEdge_zero_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ (1 : Fin 2)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 1).hom ≫
        stdSimplex.map (SimplexCategory.mkHom twistedArrowSourceEdgeOrderHom) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (twistedArrowConstantEdgeOrderHom 0)) := by
  apply edgewiseWeight_reindex_comp_map
  intro i
  fin_cases i
  · change twistedArrowSourceEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 0 0)) = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_left]
    rfl
  · change twistedArrowSourceEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 0 0)) = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_right]
    rfl

/-- 元の Tw 辺の指定端点を、同じ重みの標準表示で回収する。 -/
lemma twistedArrowSourceEdge_one_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ (0 : Fin 2)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 1).hom ≫
        stdSimplex.map (SimplexCategory.mkHom twistedArrowSourceEdgeOrderHom) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (OrderHom.id)) := by
  apply edgewiseWeight_reindex_comp_map
  intro i
  fin_cases i
  · change twistedArrowSourceEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 0 0)) = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_left]
    rfl
  · change twistedArrowSourceEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 0 0)) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_right]
    rfl

/-- 元の Tw 辺の指定端点を、同じ重みの標準表示で回収する。 -/
lemma twistedArrowTargetEdge_zero_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ (1 : Fin 2)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 1).hom ≫
        stdSimplex.map (SimplexCategory.mkHom twistedArrowTargetEdgeOrderHom) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (twistedArrowConstantEdgeOrderHom 1)) := by
  apply edgewiseWeight_reindex_comp_map
  intro i
  fin_cases i
  · change twistedArrowTargetEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 0 0)) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_left]
    rfl
  · change twistedArrowTargetEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 0 0)) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_right]
    rfl

/-- 元の Tw 辺の指定端点を、同じ重みの標準表示で回収する。 -/
lemma twistedArrowTargetEdge_one_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ (0 : Fin 2)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 1).hom ≫
        stdSimplex.map (SimplexCategory.mkHom twistedArrowTargetEdgeOrderHom) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} 0).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (OrderHom.id)) := by
  apply edgewiseWeight_reindex_comp_map
  intro i
  fin_cases i
  · change twistedArrowTargetEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 0 0)) = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_left]
    rfl
  · change twistedArrowTargetEdgeOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 0 0)) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReindexOrderHom_right]
    rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
