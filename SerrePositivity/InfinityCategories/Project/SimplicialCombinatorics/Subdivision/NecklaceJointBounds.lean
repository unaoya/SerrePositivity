module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceShape
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Fin

/-! # 元の necklace の有限 joints と直前の joint
概要：joints を元の有限頂点内の集合として読み、各頂点以下の最後の joint を作る。
方針：元の joints の零頂点を非空性の証拠とする有限最大値を使う。
規約：元の頂点番号を変えない。使われ方：全 necklace 射の joints 被覆。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
namespace NecklaceShape


/-- 元の joints を、同じ有限頂点集合の部分集合として読む。 -/
def jointVertices (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Finset T.Vertex :=
  Finset.univ.filter (fun j => j.val ∈ T.joints)

/-- 有限頂点としての joint 所属は元の joints の所属そのもの。 -/
lemma mem_jointVertices (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (j : T.Vertex) :
    j ∈ T.jointVertices ↔ j.val ∈ T.joints := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.jointVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- 元の始頂点は joint。 -/
lemma first_mem_jointVertices (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.first ∈ T.jointVertices :=
  (T.mem_jointVertices T.first).2 T.zero_mem

/-- 元の終頂点は joint。 -/
lemma last_mem_jointVertices (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.last ∈ T.jointVertices :=
  (T.mem_jointVertices T.last).2 T.last_mem

/-- 元の頂点 v 以下の joint 全体。 -/
def lowerJoints (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) : Finset T.Vertex :=
  T.jointVertices.filter (fun j => j ≤ v)

/-- 零 joint により、各頂点以下に joint が存在する。 -/
lemma lowerJoints_nonempty (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) :
    (T.lowerJoints v).Nonempty :=
  ⟨T.first, Finset.mem_filter.mpr ⟨T.first_mem_jointVertices, Fin.zero_le v⟩⟩

/-- 元の頂点 v 以下の最後の joint。 -/
def lowerJoint (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) : T.Vertex :=
  (T.lowerJoints v).max' (T.lowerJoints_nonempty v)

/-- 直前の joint は元の joint。 -/
lemma lowerJoint_mem (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) : (T.lowerJoint v).val ∈ T.joints :=
  (T.mem_jointVertices _).1
    (Finset.mem_filter.mp ((T.lowerJoints v).max'_mem (T.lowerJoints_nonempty v))).1

/-- 直前の joint は元の頂点以下。 -/
lemma lowerJoint_le (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) : T.lowerJoint v ≤ v :=
  (Finset.mem_filter.mp ((T.lowerJoints v).max'_mem (T.lowerJoints_nonempty v))).2

/-- v 以下のすべての元の joints は、同じ直前の joint 以下。 -/
lemma le_lowerJoint (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v j : T.Vertex) (hj : j.val ∈ T.joints)
    (hjv : j ≤ v) : j ≤ T.lowerJoint v :=
  (T.lowerJoints v).le_max' j (Finset.mem_filter.mpr ⟨(T.mem_jointVertices j).2 hj, hjv⟩)

end NecklaceShape
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
