module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.NecklaceVertexOrder
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceJointBounds

/-! # 元の全 necklace 射による joints の被覆
概要：標的のすべての joints が、元の始域の joints の像に入ることを証明する。
方針：bead 内の辺の像は joint を跨がず、有限 joints の最初の閾値点で像を検出する。
規約：joints 保存を射の追加条件にしない。使われ方：部分集合による立方体作用。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の bead 内の二頂点の像は、標的の内部 joint を跨がない。 -/
lemma necklaceVertexMap_noInterior {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    (a b : T.down.Vertex) (hab : a ≤ b)
    (hj : ∀ k ∈ T.down.joints, ¬ (a.val < k ∧ k < b.val)) :
    ∀ k ∈ U.down.joints,
      ¬ ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a).val < k ∧ k < (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f b).val) := by
  intro k hk
  let e := T.down.edge.{u} a b hab hj
  have h := (f.map.app _ e).property (0 : Fin 2) (Fin.last 1) k hk
  change ¬ (((f.map.app _ e).val 0).val < k ∧
    k < ((f.map.app _ e).val (Fin.last 1)).val) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_simplex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_simplex] at h
  exact h

/-- 元の標的の全 joints は、元の始域の joints の像で被覆される。 -/
lemma necklaceVertexMap_joint_covered {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    (v : U.down.Vertex) (hv : v.val ∈ U.down.joints) :
    ∃ j : T.down.Vertex, j.val ∈ T.down.joints ∧ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f j = v := by
  let s := T.down.jointVertices.filter (fun j => v.val ≤ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f j).val)
  have hs : s.Nonempty := by
    refine ⟨T.down.last, Finset.mem_filter.mpr ⟨T.down.last_mem_jointVertices, ?_⟩⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_last]
    exact Nat.le_of_lt_succ v.isLt
  let b := s.min' hs
  have hb := Finset.mem_filter.mp (s.min'_mem hs)
  have hbj : b.val ∈ T.down.joints := (T.down.mem_jointVertices b).1 hb.1
  have hkb : v.val ≤ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f b).val := hb.2
  refine ⟨b, hbj, Fin.ext ?_⟩
  by_contra hne
  have hgt : v.val < (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f b).val := by omega
  have hbpos : 0 < b.val := by
    by_contra h
    have hbf : b = T.down.first := by
      apply Fin.ext
      change b.val = 0
      omega
    have hbzero : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f b).val = 0 := by
      rw [hbf, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_first]
      rfl
    omega
  let p : T.down.Vertex := ⟨b.val - 1, by have h := b.isLt; omega⟩
  let a := T.down.lowerJoint p
  have haj : a.val ∈ T.down.joints := T.down.lowerJoint_mem p
  have hab : a < b := by
    have h := T.down.lowerJoint_le p
    change a.val ≤ b.val - 1 at h
    change a.val < b.val
    omega
  have hfa : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a).val < v.val := by
    by_contra h
    have ha : a ∈ s := Finset.mem_filter.mpr
      ⟨(T.down.mem_jointVertices a).2 haj, by omega⟩
    have hba : b ≤ a := s.min'_le a ha
    exact (not_le_of_gt hab) hba
  have hno : ∀ j ∈ T.down.joints, ¬ (a.val < j ∧ j < b.val) := by
    intro j hj hh
    let jv : T.down.Vertex := ⟨j, Nat.lt_succ_of_le (T.down.mem_le j hj)⟩
    have hjp : jv ≤ p := by
      change j ≤ b.val - 1
      omega
    have hja := T.down.le_lowerJoint p jv hj hjp
    change j ≤ a.val at hja
    omega
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_noInterior f a b hab.le hno v.val hv ⟨hfa, hgt⟩

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
