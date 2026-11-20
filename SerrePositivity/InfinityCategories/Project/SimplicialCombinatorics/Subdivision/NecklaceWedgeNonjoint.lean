module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeShape
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceNonjointCoordinates
public import Mathlib.Data.Fintype.Sum

/-! # 連結の非 joint 頂点の二ブロック分解
概要：元の連結 necklace の全非 joint 頂点を、左右の元の頂点に一意に分ける。
方針：共有頂点も joint であることから、包含の像が重ならないと示す。
規約：左と右の元の番号を保持。使われ方：dimension の加法性と cube tensor の照合。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 左の元の頂点が joint である条件は、連結後にも全く同じ。 -/
lemma wedge_joint_iff_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) :
    v.val ∈ (T.wedge U).joints ↔ v.val ∈ T.joints := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
      have hv := v.isLt
      have heq : v.val = T.vertexMax := by omega
      rw [heq]
      exact T.last_mem
  · exact T.wedge_joint_left U

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_joint_iff_left)


/-- 右の元の頂点が joint である条件は、同じ番号移動後にも全く同じ。 -/
lemma wedge_joint_iff_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : U.Vertex) :
    T.vertexMax + v.val ∈ (T.wedge U).joints ↔ v.val ∈ U.joints := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · have hb := T.mem_le _ h
      have heq : v.val = 0 := by omega
      rw [heq]
      exact U.zero_mem
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
      have heq : k = v.val := by omega
      rwa [heq] at hk
  · exact T.wedge_joint_right U

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_joint_iff_right)


/-- 元の左の非 joint 頂点の、連結後の同じ番号への単調な包含。 -/
def wedgeNonjointLeft (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.NonjointVertex →o (T.wedge U).NonjointVertex where
  toFun v := ⟨T.wedgeLeftVertex U v.val,
    fun h => v.property ((T.wedge_joint_iff_left U v.val).mp h)⟩
  monotone' _ _ h := h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointLeft)


/-- 元の右の非 joint 頂点の、共有点から番号をずらした単調な包含。 -/
def wedgeNonjointRight (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : U.NonjointVertex →o (T.wedge U).NonjointVertex where
  toFun v := ⟨T.wedgeRightVertex U v.val,
    fun h => v.property ((T.wedge_joint_iff_right U v.val).mp h)⟩
  monotone' a b h := by
    change T.vertexMax + a.val.val ≤ T.vertexMax + b.val.val
    exact Nat.add_le_add_left h _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointRight)


/-- 連結後の元の非 joint 頂点を、共有点より左右のどちらにあるかで分ける。 -/
def wedgeNonjointSplit (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : (T.wedge U).NonjointVertex) :
    T.NonjointVertex ⊕ U.NonjointVertex :=
  if h : v.val.val ≤ T.vertexMax then
    Sum.inl ⟨⟨v.val.val, by omega⟩, fun hj => v.property (T.wedge_joint_left U hj)⟩
  else
    Sum.inr ⟨⟨v.val.val - T.vertexMax, by
      have := v.val.isLt
      change v.val.val < T.vertexMax + U.vertexMax + 1 at this
      omega⟩, by
        intro hj
        have he : T.vertexMax + (v.val.val - T.vertexMax) = v.val.val := by omega
        exact v.property (he ▸ T.wedge_joint_right U hj)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointSplit)


/-- 左右の元の非 joint 頂点は、連結後の全非 joint 頂点と一対一に対応する。 -/
def wedgeNonjointEquiv (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    T.NonjointVertex ⊕ U.NonjointVertex ≃ (T.wedge U).NonjointVertex where
  toFun := Sum.elim (T.wedgeNonjointLeft U) (T.wedgeNonjointRight U)
  invFun := T.wedgeNonjointSplit U
  left_inv v := by
    rcases v with v | v
    · have h : v.val.val ≤ T.vertexMax := by
        have := v.val.isLt
        omega
      change T.wedgeNonjointSplit U (T.wedgeNonjointLeft U v) = Sum.inl v
      unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeNonjointSplit
      rw [dite_eq_left (show (T.wedgeNonjointLeft U v).val.val ≤ T.vertexMax from h)]
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Fin.ext
      rfl
    · have hv : 0 < v.val.val := by
        by_contra hn
        have he : v.val.val = 0 := by omega
        exact v.property (he ▸ U.zero_mem)
      have hh : ¬ T.vertexMax + v.val.val ≤ T.vertexMax := by omega
      change T.wedgeNonjointSplit U (T.wedgeNonjointRight U v) = Sum.inr v
      unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeNonjointSplit
      rw [dite_eq_right (show ¬ (T.wedgeNonjointRight U v).val.val ≤ T.vertexMax from hh)]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Fin.ext
      change T.vertexMax + v.val.val - T.vertexMax = v.val.val
      omega
  right_inv v := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeNonjointSplit]
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      change T.vertexMax + (v.val.val - T.vertexMax) = v.val.val
      omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointEquiv)


/-- 左の元の非 joint 頂点は、連結の共有点より厳密に左にある。 -/
lemma wedgeNonjointLeft_lt_seam (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.NonjointVertex) :
    (T.wedgeNonjointLeft U v).val.val < T.vertexMax := by
  have hn := v.val.isLt
  have he : v.val.val ≠ T.vertexMax := by
    intro h
    apply v.property
    rw [h]
    exact T.last_mem
  change v.val.val < T.vertexMax
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointLeft_lt_seam)


/-- 右の元の非 joint 頂点は、連結の共有点より厳密に右にある。 -/
lemma seam_lt_wedgeNonjointRight (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : U.NonjointVertex) :
    T.vertexMax < (T.wedgeNonjointRight U v).val.val := by
  have he : v.val.val ≠ 0 := by
    intro h
    exact v.property (h ▸ U.zero_mem)
  change T.vertexMax < T.vertexMax + v.val.val
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (seam_lt_wedgeNonjointRight)


/-- 左右の元の非 joint ブロックは、元の頂点順序で厳密に分離している。 -/
lemma wedgeNonjointLeft_lt_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape)
    (v : T.NonjointVertex) (w : U.NonjointVertex) :
    T.wedgeNonjointLeft U v < T.wedgeNonjointRight U w := by
  change (T.wedgeNonjointLeft U v).val.val < (T.wedgeNonjointRight U w).val.val
  exact lt_trans (T.wedgeNonjointLeft_lt_seam U v) (T.seam_lt_wedgeNonjointRight U w)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeNonjointLeft_lt_right)


/-- 連結の立方体の次元は、元の左右の立方体の次元の和。 -/
lemma wedge_dimension (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    (T.wedge U).dimension = T.dimension + U.dimension := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointVertex_card, ← Fintype.card_congr (T.wedgeNonjointEquiv U),
    Fintype.card_sum, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointVertex_card, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointVertex_card]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_dimension)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
