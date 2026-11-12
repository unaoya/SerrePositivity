module
public import SerrePositivity.KST.SConstruction.SimplexSubsetCoordinateInclusion
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetErase

/-! # 元の内部点削除の欠落数値座標と余次元
概要：元の削除の数値座標の像は欠ける一座標の補集合で、同じ座標の出力は零。
方針：元の昇順頂点の回収と右端からの列挙の逆律、元の削除後の濃度を使う。
規約：元の数値座標の向きを保持。使われ方：元の標準零面の判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

/-- 元の削除された内部頂点の、元の右端からの数値座標。 -/
def simplexSubsetEraseCoordinate : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.symm
    (simplexSubsetInteriorVertex I hI j hj hjm hjM)

/-- 元の欠落数値座標は、元の列挙で同じ削除頂点を回収する。 -/
lemma simplexSubsetEraseCoordinate_recovery :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate
      (simplexSubsetEraseCoordinate I hI j hj hjm hjM)).val = j :=
  (congrArg (fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v.val)
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.apply_symm_apply
      (simplexSubsetInteriorVertex I hI j hj hjm hjM))).trans
        (simplexSubsetVertexIndex_recovery I hI j hj)

/-- 元の内部頂点像が削除頂点に等しい座標は、元の同じ欠落数値座標だけ。 -/
lemma simplexSubsetEraseCoordinate_eq_iff
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val = j ↔
      i = simplexSubsetEraseCoordinate I hI j hj hjm hjM := by
  constructor
  · intro he
    apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.injective
    apply Subtype.ext
    apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective I hI
    exact he.trans (simplexSubsetEraseCoordinate_recovery I hI j hj hjm hjM).symm
  · rintro rfl
    exact simplexSubsetEraseCoordinate_recovery I hI j hj hjm hjM

/-- 元の削除の数値座標の順序埋め込みの像は、同じ欠落一座標の補集合。 -/
lemma simplexSubsetEraseCoordinate_range :
    Set.range (simplexSubsetCoordinateInclusion (I.erase j) I
      (simplexSubsetErase_two I hI j hjm hjM) hI (Finset.erase_subset _ _)
      (simplexSubsetErase_min I hI j hjm hjM) (simplexSubsetErase_max I hI j hjm hjM)) =
        {simplexSubsetEraseCoordinate I hI j hj hjm hjM}ᶜ := by
  ext i
  rw [simplexSubsetCoordinateInclusion_range]
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val ∈
    I.erase j ↔ i ≠ simplexSubsetEraseCoordinate I hI j hj hjm hjM
  rw [Finset.mem_erase]
  have hm := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val
  simp only [hm, and_true]
  exact (simplexSubsetEraseCoordinate_eq_iff I hI j hj hjm hjM i).not

/-- 元の削除の欠落数値座標での出力は、元の全ての入力に対して零。 -/
lemma simplexSubsetEraseCoordinate_zero
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom x
      (simplexSubsetEraseCoordinate I hI j hj hjm hjM) = false := by
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap _
    (fun v => x ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).nonjointCoordinate.symm v))
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate
      (simplexSubsetEraseCoordinate I hI j hj hjm hjM)) = false
  rw [simplexSubsetEraseCoordinate, Equiv.apply_symm_apply]
  exact necklaceInSimplexSubsetErase_coordinate_zero I hI j hjm hjM hj _

include hI hj hjm hjM in
/-- 元の所属内部点削除の cube は、元の全体の cube の余次元一。 -/
lemma simplexSubsetEraseCoordinate_codimension :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension + 1 := by
  have hI' := necklaceInSimplexSubset_dimension.{0} I hI
  have hE := necklaceInSimplexSubset_dimension.{0} (I.erase j)
    (simplexSubsetErase_two I hI j hjm hjM)
  have htwo := simplexSubsetErase_two I hI j hjm hjM
  have hc := Finset.card_erase_add_one hj
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension = I.card - 2 at hI'
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension = (I.erase j).card - 2 at hE
  omega

end SerrePositivity.KST.SConstruction
