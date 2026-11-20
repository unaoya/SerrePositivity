module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceSubsets
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeVertexMaps

/-! # 元の非 joint 頂点を座標とする necklace の立方体
概要：joints を含む部分集合を、元の非 joint 頂点上の Bool 値関数と順序同型で比較する。
方針：所属の指示関数と、joints を真に固定した元の全頂点の指示関数を使う。
規約：非 joint の順序付けはまだ選ばない。使われ方：実部分集合像による cubical 作用。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
namespace NecklaceShape


/-- 元の非 joint 頂点そのものを座標とする添字型。 -/
abbrev NonjointVertex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) := {v : T.Vertex // v.val ∉ T.joints}

/-- 元の joints を含む部分集合の、非 joint 座標の指示関数。 -/
def cubeSubsetBits (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (s : T.CubeSubset) : T.NonjointVertex → Bool :=
  fun v => decide (v.val ∈ s.val)

/-- 元の joints を真に固定した、元の全頂点上の指示関数。 -/
def cubeFullBits (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool) (v : T.Vertex) : Bool :=
  if h : v.val ∈ T.joints then true else b ⟨v, h⟩

/-- 非 joint 座標から、元の joints を含む頂点部分集合を回収する。 -/
def cubeSubsetFromBits (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool) : T.CubeSubset :=
  ⟨Finset.univ.filter (fun v => T.cubeFullBits b v = true), by
    intro v hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, (T.mem_jointVertices v).1 hv]⟩⟩

/-- 元の部分集合を指示関数から回収する逆律。 -/
lemma cubeSubsetFromBits_bits (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (s : T.CubeSubset) :
    T.cubeSubsetFromBits (T.cubeSubsetBits s) = s := by
  apply Subtype.ext
  ext v
  by_cases hv : v.val ∈ T.joints
  · have hs : v ∈ s.val := s.property ((T.mem_jointVertices v).2 hv)
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetFromBits, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, hv, hs]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetFromBits, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetBits, hv]

/-- 元の非 joint 座標を部分集合から回収する逆律。 -/
lemma cubeSubsetBits_fromBits (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool) :
    T.cubeSubsetBits (T.cubeSubsetFromBits b) = b := by
  funext v
  simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetBits, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetFromBits, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, v.property]

/-- 元の非 joint の指示関数は包含順序を保つ。 -/
lemma cubeSubsetBits_monotone (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Monotone T.cubeSubsetBits := by
  intro s t h v
  by_cases hs : v.val ∈ s.val
  · have ht : v.val ∈ t.val := h hs
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetBits, hs, ht]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetBits, hs]

/-- 元の部分集合への逆方向も点ごとの Bool 順序を保つ。 -/
lemma cubeSubsetFromBits_monotone (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Monotone T.cubeSubsetFromBits := by
  intro b c h v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hj : v.val ∈ T.joints
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, hj]
  · have hb : b ⟨v, hj⟩ = true := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_right hj] using (Finset.mem_filter.mp hv).2
    have hc : c ⟨v, hj⟩ = true := Bool.eq_true_of_true_le (by simpa only [hb] using h ⟨v, hj⟩)
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, hj, hc]

/-- 原典の joints を含む全頂点部分集合と、元の非 joint 座標の Bool 立方体の順序同型。 -/
def cubeSubsetBoolIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.CubeSubset ≃o (T.NonjointVertex → Bool) where
  toFun := T.cubeSubsetBits
  invFun := T.cubeSubsetFromBits
  left_inv := T.cubeSubsetFromBits_bits
  right_inv := T.cubeSubsetBits_fromBits
  map_rel_iff' := by
    intro s t
    change (T.cubeSubsetBits s ≤ T.cubeSubsetBits t) ↔ s ≤ t
    constructor
    · intro h
      have hh := T.cubeSubsetFromBits_monotone h
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetFromBits_bits] using hh
    · intro h
      exact T.cubeSubsetBits_monotone h

end NecklaceShape
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
