module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeNonjoint

/-! # 元の非 joint Bool 座標の連結
概要：左右の全非 joint 座標を、元の連結 necklace の同じ頂点へ貼る。
方針：二ブロックの全単射を使い、joint の真の値も包含で回収する。
規約：元の頂点を動かさない。使われ方：wedge 射の Bool 作用と cube tensor。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 左右の元の Bool 座標を、元の全非 joint 頂点の上で連結する。 -/
def wedgeBooleanJoin (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool)
    (c : U.NonjointVertex → Bool) : (T.wedge U).NonjointVertex → Bool :=
  fun v => Sum.elim b c ((T.wedgeNonjointEquiv U).symm v)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeBooleanJoin)


/-- 左包含への制限は元の左の Bool 座標。 -/
lemma wedgeBooleanJoin_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool)
    (c : U.NonjointVertex → Bool) (v : T.NonjointVertex) :
    T.wedgeBooleanJoin U b c (T.wedgeNonjointLeft U v) = b v := by
  change Sum.elim b c ((T.wedgeNonjointEquiv U).symm
    (T.wedgeNonjointEquiv U (Sum.inl v))) = b v
  rw [Equiv.symm_apply_apply]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeBooleanJoin_left)


/-- 右包含への制限は元の右の Bool 座標。 -/
lemma wedgeBooleanJoin_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool)
    (c : U.NonjointVertex → Bool) (v : U.NonjointVertex) :
    T.wedgeBooleanJoin U b c (T.wedgeNonjointRight U v) = c v := by
  change Sum.elim b c ((T.wedgeNonjointEquiv U).symm
    (T.wedgeNonjointEquiv U (Sum.inr v))) = c v
  rw [Equiv.symm_apply_apply]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeBooleanJoin_right)


/-- joint を真に固定した全頂点の値も、元の左包含で厳密に回収する。 -/
lemma cubeFullBits_wedge_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool)
    (c : U.NonjointVertex → Bool) (v : T.Vertex) :
    (T.wedge U).cubeFullBits (T.wedgeBooleanJoin U b c) (T.wedgeLeftVertex U v) =
      T.cubeFullBits b v := by
  by_cases h : v.val ∈ T.joints
  · have hw : (T.wedgeLeftVertex U v).val ∈ (T.wedge U).joints :=
      T.wedge_joint_left U h
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_left h, dite_eq_left hw]
  · have hw : (T.wedgeLeftVertex U v).val ∉ (T.wedge U).joints :=
      fun hv => h ((T.wedge_joint_iff_left U v).mp hv)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_right h, dite_eq_right hw]
    exact T.wedgeBooleanJoin_left U b c ⟨v, h⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (cubeFullBits_wedge_left)


/-- joint を真に固定した全頂点の値も、元の右包含で厳密に回収する。 -/
lemma cubeFullBits_wedge_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (b : T.NonjointVertex → Bool)
    (c : U.NonjointVertex → Bool) (v : U.Vertex) :
    (T.wedge U).cubeFullBits (T.wedgeBooleanJoin U b c) (T.wedgeRightVertex U v) =
      U.cubeFullBits c v := by
  by_cases h : v.val ∈ U.joints
  · have hw : (T.wedgeRightVertex U v).val ∈ (T.wedge U).joints :=
      T.wedge_joint_right U h
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_left h, dite_eq_left hw]
  · have hw : (T.wedgeRightVertex U v).val ∉ (T.wedge U).joints :=
      fun hv => h ((T.wedge_joint_iff_right U v).mp hv)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_right h, dite_eq_right hw]
    exact T.wedgeBooleanJoin_right U b c ⟨v, h⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (cubeFullBits_wedge_right)


/-- 元の連結後の全頂点は左右のどちらかの元の頂点から来る。 -/
lemma wedgeVertex_cases (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : (T.wedge U).Vertex) :
    (∃ a, T.wedgeLeftVertex U a = v) ∨ (∃ b, T.wedgeRightVertex U b = v) := by
  by_cases h : v.val ≤ T.vertexMax
  · exact Or.inl ⟨⟨v.val, by omega⟩, Fin.ext rfl⟩
  · have hn := v.isLt
    change v.val < T.vertexMax + U.vertexMax + 1 at hn
    exact Or.inr ⟨⟨v.val - T.vertexMax, by omega⟩, Fin.ext (by
      change T.vertexMax + (v.val - T.vertexMax) = v.val
      omega)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeVertex_cases)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
