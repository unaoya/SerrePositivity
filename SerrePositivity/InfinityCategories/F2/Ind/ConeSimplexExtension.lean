module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeSimplexPrefix

/-!
概要：右錐の単体に同じ右頂点を一つ付け加える。
方針：左の切断と単体を保持し、右の零単体の一意な成分だけを延ばす。
規約：左単体集合の quasicategory 性は不要。
使われ方：右頂点を固定した境界の一意な充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K : SSet.{u}}

/-- 同じ右頂点を付け加えた単体。 -/
def coneSimplexAppend {n : ℕ} (s : (join K (Δ[0] : SSet.{u})) _⦋n⦌) :
    (join K (Δ[0] : SSet.{u})) _⦋n + 1⦌ :=
  ⟨⟨s.1.val, by have hs : s.1.val < n + 2 := s.1.isLt; change _ < n + 3; omega⟩, s.2.1,
    (Join.stdAugEquiv 0 _).symm (OrderHom.const _ 0)⟩

/-- 最後の面の順序写像は先頭区間の包含。 -/
lemma coneLastFace_orderHom (n : ℕ) :
    (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom =
      Join.prefixIncl (n + 2) (n + 1) (by omega) := by
  ext i
  simp [SimplexCategory.δ, Join.prefixIncl]

/-- 最後の面は左の切断を保持する。 -/
lemma coneLastFace_pullCut {n r : ℕ} (hr : r ≤ n + 1) :
    Join.pullCut (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom r = r := by
  apply Join.cut_ext (Join.pullCut_le _ _) hr
  intro i
  rw [Join.lt_pullCut_iff, coneLastFace_orderHom]
  rfl

/-- 右頂点を付け加えた単体の最後の面は、元の同じ単体。 -/
lemma coneSimplexAppend_lastFace {n : ℕ} (s : (join K (Δ[0] : SSet.{u})) _⦋n⦌) :
    (join K Δ[0]).map (SimplexCategory.δ (Fin.last (n + 1))).op (coneSimplexAppend s) = s := by
  rcases s with ⟨⟨r, hr⟩, x, y⟩
  change r < n + 2 at hr
  let α := (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
  have hc : Join.pullCut α r = r := coneLastFace_pullCut (by omega)
  change Join.simplexMap K Δ[0] α (coneSimplexAppend ⟨⟨r, hr⟩, x, y⟩) = _
  unfold coneSimplexAppend
  rw [Join.simplexMap_eq_at K Δ[0] α _ r hc]
  have he : Join.leftMapAt α r r hc = OrderHom.id := by
    ext i
    simp [Join.leftMapAt, α, coneLastFace_orderHom, Join.prefixIncl]
  refine Join.Simplex.ext _ _ (Fin.ext rfl) ?_ ?_
  · change Join.augMap K (Join.leftMapAt α r r hc) x = x
    rw [he, Join.augMap_id]
  · exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.F2.Ind
