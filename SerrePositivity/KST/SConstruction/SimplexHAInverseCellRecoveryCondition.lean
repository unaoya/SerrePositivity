module
public import SerrePositivity.KST.SConstruction.SimplexHAInverseCellDeletion
public import SerrePositivity.KST.SConstruction.SimplexHAColumnSubsetEquality
public import SerrePositivity.KST.SConstruction.SimplexHAInsertVertexDeletion

/-! # 元の部分集合 cell 回収式と全区間・頂点挿入
概要：実 cell 像と HA 鎖射の等号を述べ、全区間で供給し、同じ集合と挿入・削除へ移す。
方針：元の有限昇順列の一意性と、任意零面の cell・HA 制限を使う。
規約：回収式の前提を明記。使われ方：欠落頂点数の帰納による無条件の全 cell 回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の部分集合の実 cell 像が、元の同じ HA 鎖射を全次数で回収するという等号。 -/
def SimplexHAInverseCellRecovery {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) : Prop :=
  simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
      (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫
    (simplexHAInverseFunctor A s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexHAChainLift A s m v b hb

/-- 元の同じ終点と同じ部分集合を持つ列の間では、元の cell 回収式を移せる。 -/
lemma simplexHAInverseCellRecovery_of_subset_eq {N m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (w : Fin (n + 1) ↪o Fin (N + 1))
    (b : Fin (N + 1)) (hv : v (Fin.last m) < b) (hw : w (Fin.last n) < b)
    (h : simplexHADecodeSubset m v {b} = simplexHADecodeSubset n w {b})
    (hrec : SimplexHAInverseCellRecovery A s n w b hw) :
    SimplexHAInverseCellRecovery A s m v b hv := by
  obtain ⟨hdim, hcol⟩ := simplexHAColumn_eq_of_subset_eq v w b hv hw h
  cases hdim
  cases hcol
  exact hrec

/-- 元の全厳密区間の cell は、元の同じ HA 鎖射を全次数で回収する。 -/
lemma simplexHAInverseCellRecovery_strictInterval {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    SimplexHAInverseCellRecovery A s (b.val - a.val - 1)
      (simplexHAStrictIntervalOrder a b hab) b (simplexHAStrictIntervalOrder_last_lt a b hab) :=
  simplexHAInverseFunctor_cell_strictInterval A s a b hab

/-- 元の頂点集合が全閉区間を埋めれば、同じ元の cell の回収式を無条件に得る。 -/
lemma simplexHAInverseCellRecovery_of_full {N m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (h : simplexHADecodeSubset m v {b} = Finset.Icc (v 0) b) :
    SimplexHAInverseCellRecovery A s m v b hb := by
  have hab : v 0 < b := (v.monotone (Fin.zero_le _)).trans_lt hb
  exact simplexHAInverseCellRecovery_of_subset_eq A s v
    (simplexHAStrictIntervalOrder (v 0) b hab) b hb
    (simplexHAStrictIntervalOrder_last_lt (v 0) b hab)
    (h.trans (simplexHAStrictIntervalOrder_subset (v 0) b hab).symm)
    (simplexHAInverseCellRecovery_strictInterval A s (v 0) b hab)

/-- 元の欠落頂点を補った列で cell を回収できれば、同じ頂点を除いて元の列へ戻せる。 -/
lemma simplexHAInverseCellRecovery_insert {N m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j)
    (hjb : j < b)
    (hrec : SimplexHAInverseCellRecovery A s (m + 1) (simplexHAInsertVertexOrder v j hj) b
      (simplexHAInsertVertexOrder_last_lt v j hj b hb hjb)) :
    SimplexHAInverseCellRecovery A s m v b hb := by
  let w := simplexHAInsertVertexOrder v j hj
  let q := simplexHAInsertVertexCoordinate v j hj hfirst
  have hw := simplexHAInsertVertexOrder_last_lt v j hj b hb hjb
  have hd := simplexHAInverseFunctor_cell_delete A s m q w b hw hrec
  have he := congrArg (fun z => simplexHADecodeSubset m z {b})
    (simplexHAInsertVertexOrder_delete v j hj hfirst)
  exact simplexHAInverseCellRecovery_of_subset_eq A s v (simplexHADeleteVertexOrder m q w) b hb
    ((w.monotone (Fin.le_last _)).trans_lt hw) he.symm hd

end SerrePositivity.KST.SConstruction
