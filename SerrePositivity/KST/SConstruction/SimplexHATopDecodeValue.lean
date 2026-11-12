module
public import SerrePositivity.KST.SConstruction.SerreCubeTopGeneratorIndex
public import SerrePositivity.KST.SConstruction.SimplexHADecodeValues
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetRecursion
public import SerrePositivity.KST.SConstruction.SimplexHABeadTailValues
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

/-! # 元の全辺読み替えによる HA 成分の回収
概要：全ての自由座標を辺にした読み替えは、元の全頂点部分集合の HA 成分を回収する。
方針：元の辺保持の再帰で最右頂点を右側へ移し、零次元の一 bead 評価へ帰着する。
規約：任意の native HA 成分データを使う。使われ方：逆構成の右逆と HA 微分条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全辺読み替えの評価は、同じ全頂点部分集合・端点・次数の元の HA 成分。 -/
lemma simplexHABeadWordDecode_top_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    HEq (simplexHABeadWordValue A s
      (simplexHABeadWordDecode m (serreCubeTopGeneratorIndex m) v T hT hb))
      (s.hom (simplexHADecodeSubset m v T) (v 0) (T.max' hT)
        (-((m + T.card - 1 : ℕ) : ℤ)) (simplexHADecodeSubset_two m v T hT hb)
        (simplexHADecodeSubset_min m v T hb).symm
        (simplexHADecodeSubset_max m v T hT hb).symm (by
          have hc := simplexHADecodeSubset_card m v T hb
          have hp := Finset.card_pos.mpr hT
          omega)) := by
  induction m generalizing T with
  | zero =>
    have hI := simplexHADecodeSubset_two 0 v T hT hb
    have he := simplexHADecodeSubset_zero v T
    have hI' : 2 ≤ (insert (v 0) T).card := he ▸ hI
    have hmin : v 0 = (insert (v 0) T).min' (Finset.insert_nonempty _ T) := by
      simpa only [← he] using (simplexHADecodeSubset_min 0 v T hb).symm
    have hmax : T.max' hT = (insert (v 0) T).max' (Finset.insert_nonempty _ T) := by
      simpa only [← he] using (simplexHADecodeSubset_max 0 v T hT hb).symm
    have hbase := simplexHABeadWordValue_reindex A s rfl
      (show T.card - 1 = serreCubeGeneratorFreeDimension 0 (serreCubeTopGeneratorIndex 0) +
        T.card - 1 by simp only [serreCubeGeneratorFreeDimension, zero_add])
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)
    exact hbase.trans ((heq_of_eq (simplexHABeadTail_value A s T hT (v 0) hb
      hI' hmin hmax)).trans
        (s.hom_heq_of_indices_degree he.symm rfl rfl (by omega)))
  | succ m ih =>
    have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (m + 1))) hb
    have hc := Finset.card_insert_of_notMem hn
    exact (simplexHABeadWordDecode_edge_value A s m (serreCubeTopGeneratorIndex m)
      v T hT hb).trans
      ((ih (Fin.castSuccOrderEmb.trans v) (insert (v (Fin.last (m + 1))) T)
        (Finset.insert_nonempty _ T) (simplexHADecodePrefix_insert m v T hb)).trans
          (s.hom_heq_of_indices_degree (simplexHADecodeSubset_insert_tail m v T) rfl
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb) (by omega)))

end SerrePositivity.KST.SConstruction
