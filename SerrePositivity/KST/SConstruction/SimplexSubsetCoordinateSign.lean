module
public import SerrePositivity.KST.SConstruction.NecklaceSingleCoordinateValue
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitCard

/-! # 元の cube 座標と HA の右側頂点数の符号
概要：元の部分集合の cube 座標に一を加えた数は、同じ頂点より右にある元の頂点数。
方針：元の右フィルターの濃度と元の一 bead の右端座標番号を照合する。
規約：元の昇順 augmentation と HA の符号を保持。使われ方：全面境界の和の添字変換。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の厳密な右フィルターに切断頂点を一つ加えると、元の右フィルターの濃度になる。 -/
lemma simplexSubsetStrictRight_card {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) :
    (I.filter (j < ·)).card + 1 = (I.filter (j ≤ ·)).card := by
  have he : (I.filter (j ≤ ·)).erase j = I.filter (j < ·) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hkj, hk, hle⟩
      exact ⟨hk, lt_of_le_of_ne hle (Ne.symm hkj)⟩
    · rintro ⟨hk, hlt⟩
      exact ⟨Ne.symm hlt.ne, hk, hlt.le⟩
  exact (congrArg (fun s => s.card + 1) he).symm.trans
    (Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hj, le_rfl⟩))

/-- 元の cube の座標に一を加えた数は、元の対応頂点より右にある部分集合の頂点数。 -/
lemma simplexSubsetCoordinate_right_count {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension) :
    (I.filter (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val < ·)).card = i.val + 1 := by
  let v := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i
  let j := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v.val
  have hj : j ∈ I := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v.val
  have hb := simplexSubsetNonjoint_bounds I hI v
  have hR := simplexSubsetSplitRight_two I hI j hj hb.2
  have hr := simplexSubsetSplitRight_card I hI j hj hR
  have he := simplexSubsetVertexIndex_order I hI v.val
  have hs := simplexSubsetStrictRight_card I j hj
  have hv := necklaceSingleCoordinate_val (I.card - 1) i
  change v.val.val + i.val + 1 = I.card - 1 at hv
  change simplexSubsetVertexIndex I hI j hj = v.val at he
  rw [he] at hr
  change (I.filter (j < ·)).card = i.val + 1
  omega

/-- 元の cube 面の符号は、元の HA の同じ頂点の右側頂点数の符号そのもの。 -/
lemma simplexSubsetCoordinate_sign {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension) :
    ((i.val + 1 : ℕ) : ℤ).negOnePow =
      ((I.filter (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val < ·)).card : ℤ).negOnePow :=
  congrArg (fun k : ℕ => (k : ℤ).negOnePow)
    (simplexSubsetCoordinate_right_count I hI i).symm

end SerrePositivity.KST.SConstruction
