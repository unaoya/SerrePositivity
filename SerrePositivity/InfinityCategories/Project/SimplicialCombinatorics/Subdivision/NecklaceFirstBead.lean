module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceShapeEquality
public import Mathlib.Data.Finset.Max

/-! # 元の最初の bead と残りの necklace
概要：最初の正の joint で切り、標準単体一つと残りへ厳密に分解する。
方針：有限 joints の最小正元と、その後ろの joints の番号移動を使う。
規約：元の長さを減らす。使われ方：全 necklace の preferred form の存在証明。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 元の正の joints の有限集合。 -/
def positiveJoints (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Finset ℕ := T.joints.filter (0 < ·)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (positiveJoints)


/-- 点以外の necklace は元の正の joint を持つ。 -/
lemma positiveJoints_nonempty (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax) :
    T.positiveJoints.Nonempty :=
  ⟨T.vertexMax, Finset.mem_filter.mpr ⟨T.last_mem, h⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (positiveJoints_nonempty)


/-- 元の最初の正の joint。 -/
def firstPositiveJoint (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax) : ℕ :=
  T.positiveJoints.min' (T.positiveJoints_nonempty h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (firstPositiveJoint)


/-- 最初の正の joint は元の joints に所属する。 -/
lemma firstPositiveJoint_mem (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax) :
    T.firstPositiveJoint h ∈ T.joints :=
  (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (firstPositiveJoint_mem)


/-- 最初の正の joint は零ではない。 -/
lemma firstPositiveJoint_pos (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax) :
    0 < T.firstPositiveJoint h :=
  (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (firstPositiveJoint_pos)


/-- 元の任意の正の joint は最初の正の joint 以降にある。 -/
lemma firstPositiveJoint_le (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax)
    (j : ℕ) (hj : j ∈ T.joints) (hp : 0 < j) : T.firstPositiveJoint h ≤ j :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj, hp⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (firstPositiveJoint_le)


/-- 元の joint から後ろを、同じ joint を新しい始点として番号付けした形。 -/
def tail (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (p : ℕ) (hp : p ∈ T.joints) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape where
  vertexMax := T.vertexMax - p
  joints := (T.joints.filter (p ≤ ·)).image (· - p)
  zero_mem := Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, le_rfl⟩, Nat.sub_self p⟩
  last_mem := Finset.mem_image.mpr ⟨T.vertexMax,
    Finset.mem_filter.mpr ⟨T.last_mem, T.mem_le p hp⟩, rfl⟩
  mem_le j hj := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Nat.sub_le_sub_right (T.mem_le k (Finset.mem_filter.mp hk).1) p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (tail)


/-- 最初の正の joint で切ると、元の標準単体一つと残りの連結に厳密に等しい。 -/
lemma single_wedge_tail (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (p : ℕ) (hp : p ∈ T.joints)
    (hm : ∀ j ∈ T.joints, 0 < j → p ≤ j) : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (T.tail p hp) = T := by
  have hpn := T.mem_le p hp
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.shape_ext (by change p + (T.vertexMax - p) = T.vertexMax; omega)
  apply Finset.ext
  intro j
  change j ∈ ({0, p} ∪ ((T.joints.filter (p ≤ ·)).image (· - p)).image (p + ·)) ↔ _
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ((rfl | rfl) | ⟨k, ⟨l, hl, rfl⟩, rfl⟩)
    · exact T.zero_mem
    · exact hp
    · have hlp := (Finset.mem_filter.mp hl).2
      have he : p + (l - p) = l := by omega
      rw [he]
      exact (Finset.mem_filter.mp hl).1
  · intro hj
    by_cases h0 : j = 0
    · exact Or.inl (Or.inl h0)
    · have hpj := hm j hj (by omega)
      exact Or.inr ⟨j - p, ⟨j, Finset.mem_filter.mpr ⟨hj, hpj⟩, rfl⟩, by omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (single_wedge_tail)


/-- 最初の正の joint で切った残りは、元の長さより厳密に短い。 -/
lemma firstPositive_tail_lt (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (h : 0 < T.vertexMax) :
    (T.tail (T.firstPositiveJoint h) (T.firstPositiveJoint_mem h)).vertexMax < T.vertexMax := by
  have hp := T.firstPositiveJoint_pos h
  change T.vertexMax - T.firstPositiveJoint h < T.vertexMax
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (firstPositive_tail_lt)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
