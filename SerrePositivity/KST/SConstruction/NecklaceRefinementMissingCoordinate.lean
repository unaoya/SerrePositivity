module
public import SerrePositivity.KST.SConstruction.NecklaceRefinementCoordinates

/-! # 元の三 joint refinement の欠落数値座標
概要：元の内部 joint が一つなら、元の座標包含の像は一座標の補集合で、その出力は一。
方針：元の joints の全所属条件・反順列挙・有限集合の一元削除の濃度を使う。
規約：元の局所頂点と右端からの座標を保持。使われ方：分割合成の標準一面の判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
variable (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (j : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex)

/-- 元の三 joint 模型では、出力の内部頂点が元の joint なのは指定の中間頂点だけ。 -/
lemma necklaceRefinement_joint_iff
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax})
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex) :
    v.val.val ∈ T.down.joints ↔ v = j := by
  have hv : v.val.val ≠ 0 ∧ v.val.val ≠ T.down.vertexMax := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton, not_or]
      using v.property
  rw [hJ]
  simp only [Finset.mem_insert, Finset.mem_singleton, hv.1, hv.2, false_or, or_false]
  exact ⟨fun h => Subtype.ext (Fin.ext h), fun h => congrArg (fun w => w.val.val) h⟩

/-- 元の指定中間頂点の、同じ右端からの数値座標。 -/
def necklaceRefinementMissingCoordinate :
    Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.symm j

/-- 元の内部頂点が指定中間頂点になる数値座標は、元の同じ欠落座標だけ。 -/
lemma necklaceRefinementMissingCoordinate_eq_iff
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate i = j ↔
      i = necklaceRefinementMissingCoordinate T j := by
  constructor
  · intro h
    exact ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.symm_apply_apply i).symm.trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.symm h)
  · rintro rfl
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.apply_symm_apply j

/-- 元の三 joint refinement の数値座標の像は、同じ中間頂点の一座標だけを欠く。 -/
lemma necklaceRefinementMissingCoordinate_range
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    Set.range (necklaceRefinementCoordinate T) = {necklaceRefinementMissingCoordinate T j}ᶜ := by
  ext i
  rw [necklaceRefinementCoordinate_range]
  change ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate i).val.val ∉ T.down.joints ↔
    i ≠ necklaceRefinementMissingCoordinate T j
  exact ((necklaceRefinement_joint_iff T j hJ _).trans
    (necklaceRefinementMissingCoordinate_eq_iff T j i)).not

/-- 元の中間 joint の数値座標での出力は、元の全入力に対して一。 -/
lemma necklaceRefinementMissingCoordinate_one
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (necklaceBeadRefinement T) x (necklaceRefinementMissingCoordinate T j) =
      true := by
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap _ (fun v => x (T.down.nonjointCoordinate.symm v))
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate
      (necklaceRefinementMissingCoordinate T j)) = true
  have hc := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.apply_symm_apply j
  have hj : j.val.val ∈ T.down.joints := (necklaceRefinement_joint_iff T j hJ j).mpr rfl
  exact (congrArg (fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (necklaceBeadRefinement T)
    (fun w => x (T.down.nonjointCoordinate.symm w)) v) hc).trans
      ((necklaceBeadRefinement_boolean T _ j).trans (dite_eq_left hj))

/-- 元の内部 joint が一つの refinement は、元の cube の余次元一。 -/
lemma necklaceRefinementMissingCoordinate_codimension
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension = T.down.dimension + 1 := by
  have hs : T.down.nonjointNumbers =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointNumbers.erase j.val.val := by
    ext k
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumbers, Finset.mem_erase, Finset.mem_filter,
      hJ, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  have hj : j.val.val ∈ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointNumbers :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.val.isLt, j.property⟩
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointNumbers.card =
    T.down.nonjointNumbers.card + 1
  rw [hs]
  exact (Finset.card_erase_add_one hj).symm

end SerrePositivity.KST.SConstruction
