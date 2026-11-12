module
public import SerrePositivity.KST.SConstruction.SimplexHABeadTailCells
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCellAtDimension

/-! # 元の右側頂点を持つ語と部分集合の実生成射の比較
概要：右側集合と左端点から作った元の語の実鎖射は、同じ部分集合生成射に戻る。
方針：元の語の実鎖射の式と、指定次元・端点の生成射の回収を合成する。
規約：元の移送だけを異種等号で外す。使われ方：標準面との帰納的比較の基底。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右側集合を持つ語の実鎖射は、同じ部分集合の元の実生成射と異種等号で一致。 -/
lemma simplexHABeadTail_cell_canonical_heq {n : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (a : Fin (n + 1)) (ha : ∀ t ∈ T, a < t)
    (hI : 2 ≤ (insert a T).card)
    (hmin : a = (insert a T).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI))
    (hmax : T.max' hT = (insert a T).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI)) :
    HEq (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT a ha))
      (simplexSubsetLambdaCell A (insert a T) hI) := by
  have h := simplexHABeadTail_cell A T hT a ha hI hmin hmax
  have hd : T.card - 1 = (insert a T).card - 2 := by
    have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha)
    omega
  exact (heq_of_eq h).trans
    (simplexSubsetLambdaCellAtDimension_canonical_heq A _ _ _ _ _ _ _ hd)

end SerrePositivity.KST.SConstruction
