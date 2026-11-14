module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceShape

/-! # necklace の連結と切断頂点
概要：終点と始点を共有する二つの有限 necklace を連結する。
方針：右側の番号を左側の長さだけずらし、共有頂点を joint に残す。
規約：点も許す。使われ方：実単体集合の wedge と cubical 合成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 両端を一つの joint で貼った、元の有限 necklace の形。 -/
def wedge (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape where
  vertexMax := T.vertexMax + U.vertexMax
  joints := T.joints ∪ U.joints.image (fun j => T.vertexMax + j)
  zero_mem := Finset.mem_union_left _ T.zero_mem
  last_mem := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, U.last_mem, rfl⟩)
  mem_le j hj := by
    rcases Finset.mem_union.mp hj with hj | hj
    · have := T.mem_le j hj; omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have := U.mem_le k hk
      omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge)


/-- 左側の全 joint は連結後も joint。 -/
lemma wedge_joint_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {j : ℕ} (hj : j ∈ T.joints) :
    j ∈ (T.wedge U).joints := Finset.mem_union_left _ hj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_joint_left)


/-- 右側の全 joint は同じ番号移動で連結後の joint。 -/
lemma wedge_joint_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {j : ℕ} (hj : j ∈ U.joints) :
    T.vertexMax + j ∈ (T.wedge U).joints :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hj, rfl⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_joint_right)


/-- 共有する元の終始点は連結後の joint。 -/
lemma wedge_joint_seam (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.vertexMax ∈ (T.wedge U).joints :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_left T U T.last_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_joint_seam)


/-- 左頂点の元の番号を保持する単調な包含。 -/
def wedgeLeftVertex (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.Vertex →o (T.wedge U).Vertex where
  toFun v := ⟨v.val, by have := v.isLt; change _ < T.vertexMax + U.vertexMax + 1; omega⟩
  monotone' _ _ h := h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeLeftVertex)


/-- 右頂点を共有頂点から番号付けする単調な包含。 -/
def wedgeRightVertex (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : U.Vertex →o (T.wedge U).Vertex where
  toFun v := ⟨T.vertexMax + v.val, by have := v.isLt; exact Nat.add_lt_add_left this _⟩
  monotone' _ _ h := Nat.add_le_add_left h _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeRightVertex)


/-- 右側を共有終点へ潰す単調な射影。 -/
def wedgeLeftClamp (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.wedge U).Vertex →o T.Vertex where
  toFun v := ⟨min v.val T.vertexMax, by omega⟩
  monotone' a b h := by
    change min a.val T.vertexMax ≤ min b.val T.vertexMax
    exact min_le_min_right _ h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeLeftClamp)


/-- 左側を共有始点へ潰す単調な射影。 -/
def wedgeRightClamp (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.wedge U).Vertex →o U.Vertex where
  toFun v := ⟨v.val - T.vertexMax, by
    have := v.isLt
    change v.val < T.vertexMax + U.vertexMax + 1 at this
    omega⟩
  monotone' _ _ h := Nat.sub_le_sub_right h _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeRightClamp)


/-- 左側の bead 条件は連結後にも成立する。 -/
lemma wedge_allows_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ} {s : Fin (n + 1) → T.Vertex}
    (hs : T.Allows s) : (T.wedge U).Allows (T.wedgeLeftVertex U ∘ s) := by
  intro i j k hk h
  change (s i).val < k ∧ k < (s j).val at h
  rcases Finset.mem_union.mp hk with hk | hk
  · exact hs i j k hk h
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have := (s j).isLt
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_allows_left)


/-- 右側の bead 条件は連結後にも成立する。 -/
lemma wedge_allows_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ} {s : Fin (n + 1) → U.Vertex}
    (hs : U.Allows s) : (T.wedge U).Allows (T.wedgeRightVertex U ∘ s) := by
  intro i j k hk h
  change T.vertexMax + (s i).val < k ∧ k < T.vertexMax + (s j).val at h
  rcases Finset.mem_union.mp hk with hk | hk
  · have := T.mem_le k hk; omega
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    apply hs i j l hl
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_allows_right)


/-- 左への射影はすべての bead 条件を保つ。 -/
lemma wedge_allows_leftClamp (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    {s : Fin (n + 1) → (T.wedge U).Vertex} (hs : (T.wedge U).Allows s) :
    T.Allows (T.wedgeLeftClamp U ∘ s) := by
  intro i j k hk h
  change min (s i).val T.vertexMax < k ∧ k < min (s j).val T.vertexMax at h
  have := T.mem_le k hk
  apply hs i j k (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_left T U hk)
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_allows_leftClamp)


/-- 右への射影はすべての bead 条件を保つ。 -/
lemma wedge_allows_rightClamp (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    {s : Fin (n + 1) → (T.wedge U).Vertex} (hs : (T.wedge U).Allows s) :
    U.Allows (T.wedgeRightClamp U ∘ s) := by
  intro i j k hk h
  change (s i).val - T.vertexMax < k ∧ k < (s j).val - T.vertexMax at h
  apply hs i j (T.vertexMax + k) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_right T U hk)
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_allows_rightClamp)


/-- 連結後の各単体は、左側か右側の一方に全体が入る。 -/
lemma wedge_allows_split (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    {s : Fin (n + 1) → (T.wedge U).Vertex} (hs : (T.wedge U).Allows s) :
    (∀ i, (s i).val ≤ T.vertexMax) ∨ (∀ i, T.vertexMax ≤ (s i).val) := by
  classical
  by_cases h : ∀ i, (s i).val ≤ T.vertexMax
  · exact Or.inl h
  · right
    obtain ⟨j, hj⟩ := not_forall.mp h
    intro i
    have := hs i j T.vertexMax (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_seam T U)
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_allows_split)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftClamp (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeLeftClamp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftClamp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeLeftVertex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightClamp (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightClamp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightClamp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightVertex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_allows_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_allows_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_allows_leftClamp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_allows_leftClamp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_allows_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_allows_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_allows_rightClamp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_allows_rightClamp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_allows_split := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_allows_split

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_joint_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_joint_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_joint_seam := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_joint_seam

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeLeftClamp._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftClamp._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeLeftClamp._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftClamp._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeLeftVertex._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeLeftVertex._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightClamp._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightClamp._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightClamp._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightClamp._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightVertex._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightVertex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeRightVertex._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeRightVertex._proof_2
