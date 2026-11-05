module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceSubsets
public import SerrePositivity.InfinityCategories.Simplicial.CubeVertexMaps

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
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
namespace NecklaceShape
open SerrePositivity.KST.SConstruction.NecklaceShape

/-- 元の非 joint 頂点そのものを座標とする添字型。 -/
abbrev NonjointVertex (T : NecklaceShape) := {v : T.Vertex // v.val ∉ T.joints}

/-- 元の joints を含む部分集合の、非 joint 座標の指示関数。 -/
def cubeSubsetBits (T : NecklaceShape) (s : T.CubeSubset) : T.NonjointVertex → Bool :=
  fun v => decide (v.val ∈ s.val)

/-- 元の joints を真に固定した、元の全頂点上の指示関数。 -/
def cubeFullBits (T : NecklaceShape) (b : T.NonjointVertex → Bool) (v : T.Vertex) : Bool :=
  if h : v.val ∈ T.joints then true else b ⟨v, h⟩

/-- 非 joint 座標から、元の joints を含む頂点部分集合を回収する。 -/
def cubeSubsetFromBits (T : NecklaceShape) (b : T.NonjointVertex → Bool) : T.CubeSubset :=
  ⟨Finset.univ.filter (fun v => T.cubeFullBits b v = true), by
    intro v hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [cubeFullBits, (T.mem_jointVertices v).1 hv]⟩⟩

/-- 元の部分集合を指示関数から回収する逆律。 -/
lemma cubeSubsetFromBits_bits (T : NecklaceShape) (s : T.CubeSubset) :
    T.cubeSubsetFromBits (T.cubeSubsetBits s) = s := by
  apply Subtype.ext
  ext v
  by_cases hv : v.val ∈ T.joints
  · have hs : v ∈ s.val := s.property ((T.mem_jointVertices v).2 hv)
    simp [cubeSubsetFromBits, cubeFullBits, hv, hs]
  · simp [cubeSubsetFromBits, cubeFullBits, cubeSubsetBits, hv]

/-- 元の非 joint 座標を部分集合から回収する逆律。 -/
lemma cubeSubsetBits_fromBits (T : NecklaceShape) (b : T.NonjointVertex → Bool) :
    T.cubeSubsetBits (T.cubeSubsetFromBits b) = b := by
  funext v
  simp [cubeSubsetBits, cubeSubsetFromBits, cubeFullBits, v.property]

/-- 元の非 joint の指示関数は包含順序を保つ。 -/
lemma cubeSubsetBits_monotone (T : NecklaceShape) : Monotone T.cubeSubsetBits := by
  intro s t h v
  by_cases hs : v.val ∈ s.val
  · have ht : v.val ∈ t.val := h hs
    simp [cubeSubsetBits, hs, ht]
  · simp [cubeSubsetBits, hs]

/-- 元の部分集合への逆方向も点ごとの Bool 順序を保つ。 -/
lemma cubeSubsetFromBits_monotone (T : NecklaceShape) : Monotone T.cubeSubsetFromBits := by
  intro b c h v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hj : v.val ∈ T.joints
  · simp [cubeFullBits, hj]
  · have hb : b ⟨v, hj⟩ = true := by
      simpa only [cubeFullBits, dite_eq_right hj] using (Finset.mem_filter.mp hv).2
    have hc : c ⟨v, hj⟩ = true := Bool.eq_true_of_true_le (by simpa only [hb] using h ⟨v, hj⟩)
    simp [cubeFullBits, hj, hc]

/-- 原典の joints を含む全頂点部分集合と、元の非 joint 座標の Bool 立方体の順序同型。 -/
def cubeSubsetBoolIso (T : NecklaceShape) : T.CubeSubset ≃o (T.NonjointVertex → Bool) where
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
      simpa only [cubeSubsetFromBits_bits] using hh
    · intro h
      exact T.cubeSubsetBits_monotone h

end NecklaceShape
end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.NonjointVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.NonjointVertex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.NonjointVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeFullBits := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBits (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBits := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBits_fromBits := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBits_fromBits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBits_monotone := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBits_monotone

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBoolIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBoolIso := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBoolIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetFromBits := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetFromBits_bits := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits_bits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetFromBits_monotone := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits_monotone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeFullBits.eq_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBits.eq_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBits.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetBoolIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetBoolIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetFromBits._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.cubeSubsetFromBits.eq_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits.eq_1
