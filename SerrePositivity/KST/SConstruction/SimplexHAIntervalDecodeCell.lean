module
public import SerrePositivity.KST.SConstruction.NecklaceClosedIntervalSubset
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaNecklaceCell
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaCell
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCell
public import SerrePositivity.KST.SConstruction.SimplexHAStrictIntervalOrder

/-! # 元の全区間 HA 部分集合生成射と実 Hom 同型
概要：元の厳密区間の全頂点を持つ HA 生成射は、同じ元の Λ Hom 同型の順射。
方針：同じ閉区間の augmentation 等号と、両生成射の元の次元移送を照合する。
規約：元の全頂点・端点・全次数を保持。使われ方：native HA 逆 dg 関手の全 Hom 逆律。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の閉区間部分集合の指定次元生成射は、同じ区間 Hom 同型の順射と異種等号で一致。 -/
lemma simplexSubsetLambdaCellAtDimension_closedInterval_heq {N : ℕ}
    (a b : Fin (N + 1)) (hab : a ≤ b) (hI : 2 ≤ (Finset.Icc a b).card)
    (ha : a = (Finset.Icc a b).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI))
    (hb : b = (Finset.Icc a b).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI))
    (d : ℕ) (hd : d = (Finset.Icc a b).card - 2) :
    HEq (simplexSubsetLambdaCellAtDimension A (Finset.Icc a b) a b hI ha hb d hd)
      (simplexIntervalLambdaHomIso A a b hab).hom :=
  (simplexSubsetLambdaCellAtDimension_necklace_heq A _ _ _ _ _ _ _ _).trans
    ((necklaceLambdaCell_heq_of_eq A
      (necklaceInSimplexSubsetAt_closedInterval a b hab hI ha hb)).trans
        ((heq_of_eq (simplexIntervalLambdaHomIso_cell A a b hab)).trans
          (eqToHom_comp_heq _ _)).symm)

/-- 元の厳密区間の HA 部分集合生成射は、元の同じ区間 Hom 同型の順射そのもの。 -/
lemma simplexHADecodeSubsetCell_strictInterval {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    simplexHADecodeSubsetCell A (b.val - a.val - 1) (simplexHAStrictIntervalOrder a b hab)
      {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ simplexHAStrictIntervalOrder_last_lt a b hab) =
        (simplexIntervalLambdaHomIso A a b hab.le).hom := by
  have hI := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_two a b hab
  have ha := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_min a b hab.le (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI)
  have hb := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_max a b hab.le (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI)
  have hd : b.val - a.val - 1 = (Finset.Icc a b).card - 2 := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab.le]
    omega
  have h₀ := simplexHADecodeSubsetCell_canonical_heq A (b.val - a.val - 1)
    (simplexHAStrictIntervalOrder a b hab) {b} (Finset.singleton_nonempty b)
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ simplexHAStrictIntervalOrder_last_lt a b hab)
  have hDecoded : 2 ≤ (simplexHADecodeSubset (b.val - a.val - 1)
      (simplexHAStrictIntervalOrder a b hab) {b}).card := by
    rw [simplexHAStrictIntervalOrder_subset a b hab]
    exact hI
  have h₁ := simplexSubsetLambdaCell_heq_of_eq A _ _
    (simplexHAStrictIntervalOrder_subset a b hab) hDecoded hI
  have h₂ := simplexSubsetLambdaCellAtDimension_canonical_heq A (Finset.Icc a b) a b hI ha hb
    (b.val - a.val - 1) hd
  exact eq_of_heq (h₀.trans (h₁.trans (h₂.symm.trans
    (simplexSubsetLambdaCellAtDimension_closedInterval_heq A a b hab.le hI ha hb _ hd))))

end SerrePositivity.KST.SConstruction
