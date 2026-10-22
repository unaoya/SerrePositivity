module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeSimplexExtension
public import SerrePositivity.InfinityCategories.F2.Ind.CodiscreteConeCut

/-!
概要：右頂点を最後の頂点に持つ錐の単体は、最後の面から一意に回収できる。
方針：最後の面の切断と左成分を計算し、右成分の一意性を使う。
規約：左因子の充填性は仮定しない。
使われ方：右頂点を固定した任意の境界の充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K : SSet.{u}}

/-- 切断が最後の頂点より前なら、最後の面に右頂点を付け加えると元に戻る。 -/
lemma coneSimplex_eq_append_lastFace {n : ℕ}
    (s : (join K (Δ[0] : SSet.{u})) _⦋n + 1⦌) (hs : s.1.val ≤ n + 1) :
    coneSimplexAppend ((join K Δ[0]).map
      (SimplexCategory.δ (Fin.last (n + 1))).op s) = s := by
  rcases s with ⟨⟨r, hr⟩, x, y⟩
  change r ≤ n + 1 at hs
  let α := (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
  have hc : Join.pullCut α r = r := coneLastFace_pullCut hs
  change coneSimplexAppend (Join.simplexMap K Δ[0] α ⟨⟨r, hr⟩, x, y⟩) = _
  rw [Join.simplexMap_eq_at K Δ[0] α _ r hc]
  have he : Join.leftMapAt α r r hc = OrderHom.id := by
    ext i
    simp [Join.leftMapAt, α, coneLastFace_orderHom, Join.prefixIncl]
  refine Join.Simplex.ext _ _ (Fin.ext rfl) ?_ ?_
  · change Join.augMap K (Join.leftMapAt α r r hc) x = x
    rw [he, Join.augMap_id]
  · exact Subsingleton.elim _ _

/-- 最後の面を取る写像は、最後の頂点が右側にある単体で単射。 -/
lemma coneLastFace_injective {n : ℕ}
    {s t : (join K (Δ[0] : SSet.{u})) _⦋n + 1⦌}
    (hs : s.1.val ≤ n + 1) (ht : t.1.val ≤ n + 1)
    (h : (join K Δ[0]).map (SimplexCategory.δ (Fin.last (n + 1))).op s =
      (join K Δ[0]).map (SimplexCategory.δ (Fin.last (n + 1))).op t) : s = t := by
  rw [← coneSimplex_eq_append_lastFace s hs, ← coneSimplex_eq_append_lastFace t ht, h]

/-- 錐の同じ右頂点。 -/
def coneApex (K : SSet.{u}) : (join K (Δ[0] : SSet.{u})) _⦋0⦌ :=
  (joinInr K Δ[0]).app _ (stdSimplex.obj₀Equiv.symm 0)

/-- 零単体の切断が零であることは、右頂点との一致と同値。 -/
lemma coneVertex_eq_apex_iff (s : (join K (Δ[0] : SSet.{u})) _⦋0⦌) :
    s = coneApex K ↔ s.1.val = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hs
    refine Join.Simplex.ext _ _ (Fin.ext hs) ?_ ?_
    · exact @Subsingleton.elim PUnit inferInstance _ _
    · exact Subsingleton.elim _ _

/-- 指定した頂点が右頂点に一致する条件。 -/
lemma coneSimplexVertex_eq_apex_iff {n : ℕ}
    (s : (join K (Δ[0] : SSet.{u})) _⦋n⦌) (i : Fin (n + 1)) :
    coneSimplexVertex s i = coneApex K ↔ s.1.val ≤ i.val := by
  rw [coneVertex_eq_apex_iff, coneSimplexVertex_cut]

end SerrePositivity.InfinityCategories.F2.Ind
