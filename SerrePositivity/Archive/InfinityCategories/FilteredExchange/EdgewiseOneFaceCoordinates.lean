module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates

/-!
概要：共通解像の一次元の両面を標準三単体の二頂点の包含として計算する。
方針：F1 の左右頂点の添字変換を零次元に特殊化する。
規約：実際の重みの添字変換を保持する。
使われ方：元の精密化を保持する二辺の実両端の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 面 0 は外側の (0,3)、面 1 は内側の (1,2) の二頂点を選ぶ。 -/
def edgewiseOneFaceInclusion (i : Fin 2) : Fin 2 →o Fin 4 where
  toFun j := if j = 0 then ⟨i.val, by omega⟩ else ⟨3 - i.val, by omega⟩
  monotone' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> fin_cases i <;> simp_all

/-- 共通解像の一次元の実両面は同じ二頂点の標準包含。 -/
lemma edgewiseWeightStandardMap_one_face (i : Fin 2) :
    edgewiseWeightStandardMap.{u} (SimplexCategory.δ i) =
      stdSimplex.map (SimplexCategory.mkHom (edgewiseOneFaceInclusion i)) := by
  have h : edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ i) =
      edgewiseOneFaceInclusion i := by
    ext j
    fin_cases j
    · have hl := edgewiseWeightReindexOrderHom_left.{u} (SimplexCategory.δ i) (0 : Fin 1)
      change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ i) 0 = _ at hl
      change (edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ i) 0).val =
        (edgewiseOneFaceInclusion i 0).val
      rw [hl]
      fin_cases i <;> rfl
    · have hr := edgewiseWeightReindexOrderHom_right.{u} (SimplexCategory.δ i) (0 : Fin 1)
      change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ i) 1 = _ at hr
      change (edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ i) 1).val =
        (edgewiseOneFaceInclusion i 1).val
      rw [hr]
      fin_cases i <;> rfl
  rw [← edgewiseWeightReindexOrderHom_map, h]

/-- 元の重みの両面を標準単体へ移すと同じ二頂点の包含。 -/
lemma edgewiseWeight_one_face (i : Fin 2) :
    edgewiseWeight.map (SimplexCategory.δ i) ≫ (edgewiseWeightIso.{u} 1).hom =
      (edgewiseWeightIso 0).hom ≫
        stdSimplex.map (SimplexCategory.mkHom (edgewiseOneFaceInclusion i)) := by
  rw [← edgewiseWeightStandardMap_one_face, edgewiseWeightStandardMap,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
