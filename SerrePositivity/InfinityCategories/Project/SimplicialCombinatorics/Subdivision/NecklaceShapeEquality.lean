module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeShape

/-! # necklace の形の等号と一点単位
概要：同じ長さと同じ joints を持つ形を厳密に同一視する。
方針：証明成分の一意性と有限集合の所属で判定する。
規約：頂点の番号を保持する。使われ方：preferred bead 分解と wedge の単位。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 元の長さと joints の等号から、証明成分を含む形の等号を得る。 -/
@[ext] theorem shape_ext {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (hn : T.vertexMax = U.vertexMax)
    (hj : T.joints = U.joints) : T = U := by
  cases T
  cases U
  cases hn
  cases hj
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (shape_ext)


/-- 長さ零の元の necklace は一点の形そのもの。 -/
lemma eq_single_zero (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : T.vertexMax = 0) : T = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.shape_ext h
  apply Finset.ext
  intro j
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton, or_self]
  constructor
  · intro hj
    have := T.mem_le j hj
    omega
  · rintro rfl
    exact T.zero_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (eq_single_zero)


/-- 元の一点を左に貼っても、同じ全頂点と joints の形を回収する。 -/
lemma single_zero_wedge (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0).wedge T = T := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.shape_ext (Nat.zero_add _)
  apply Finset.ext
  intro j
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Nat.zero_add, Finset.mem_image, or_self]
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact T.zero_mem
    · exact hk
  · intro hj
    exact Or.inr ⟨j, hj, rfl⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (single_zero_wedge)


/-- 元の一点を右に貼っても、同じ全頂点と joints の形を回収する。 -/
lemma wedge_single_zero (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0) = T := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.shape_ext (T := T.wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0)) (U := T) (Nat.add_zero _)
  apply Finset.ext
  intro j
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Nat.add_zero, Finset.mem_image, or_self]
  constructor
  · rintro (hj | ⟨k, rfl, rfl⟩)
    · exact hj
    · exact T.last_mem
  · exact Or.inl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_single_zero)


/-- 三つの元の necklace の連結は、長さと全 joints を保って結合する。 -/
lemma wedge_assoc (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.wedge U).wedge V = T.wedge (U.wedge V) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.shape_ext (T := (T.wedge U).wedge V) (U := T.wedge (U.wedge V))
    (Nat.add_assoc _ _ _)
  change (T.joints ∪ U.joints.image (T.vertexMax + ·)) ∪
      V.joints.image (T.vertexMax + U.vertexMax + ·) =
    T.joints ∪ (U.joints ∪ V.joints.image (U.vertexMax + ·)).image (T.vertexMax + ·)
  simp only [Finset.image_union, Finset.image_image, Function.comp_def, Nat.add_assoc,
    Finset.union_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_assoc)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
