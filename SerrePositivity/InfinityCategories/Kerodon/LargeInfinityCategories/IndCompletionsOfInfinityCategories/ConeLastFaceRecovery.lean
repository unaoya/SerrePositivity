module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeSimplexExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CodiscreteConeCut

/-!
概要：右頂点を最後の頂点に持つ錐の単体は、最後の面から一意に回収できる。
方針：最後の面の切断と左成分を計算し、右成分の一意性を使う。
規約：左因子の充填性は仮定しない。
使われ方：右頂点を固定した任意の境界の充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K : SSet.{u}}

/-- 切断が最後の頂点より前なら、最後の面に右頂点を付け加えると元に戻る。 -/
lemma coneSimplex_eq_append_lastFace {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n + 1⦌) (hs : s.1.val ≤ n + 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexAppend ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]).map
      (SimplexCategory.δ (Fin.last (n + 1))).op s) = s := by
  rcases s with ⟨⟨r, hr⟩, x, y⟩
  change r ≤ n + 1 at hs
  let α := (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r = r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneLastFace_pullCut hs
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexAppend (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap K Δ[0] α ⟨⟨r, hr⟩, x, y⟩) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at K Δ[0] α _ r hc]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α r r hc = OrderHom.id := by
    ext i
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt, α, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneLastFace_orderHom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext rfl) ?_ ?_
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α r r hc) x = x
    rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id]
  · exact Subsingleton.elim _ _

/-- 最後の面を取る写像は、最後の頂点が右側にある単体で単射。 -/
lemma coneLastFace_injective {n : ℕ}
    {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n + 1⦌}
    (hs : s.1.val ≤ n + 1) (ht : t.1.val ≤ n + 1)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]).map (SimplexCategory.δ (Fin.last (n + 1))).op s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]).map (SimplexCategory.δ (Fin.last (n + 1))).op t) : s = t := by
  rw [← coneSimplex_eq_append_lastFace s hs, ← coneSimplex_eq_append_lastFace t ht, h]

/-- 錐の同じ右頂点。 -/
def coneApex (K : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app _ (stdSimplex.obj₀Equiv.symm 0)

/-- 零単体の切断が零であることは、右頂点との一致と同値。 -/
lemma coneVertex_eq_apex_iff (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋0⦌) :
    s = coneApex K ↔ s.1.val = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hs
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext hs) ?_ ?_
    · exact @Subsingleton.elim PUnit inferInstance _ _
    · exact Subsingleton.elim _ _

/-- 指定した頂点が右頂点に一致する条件。 -/
lemma coneSimplexVertex_eq_apex_iff {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex s i = coneApex K ↔ s.1.val ≤ i.val := by
  rw [coneVertex_eq_apex_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex_cut]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
