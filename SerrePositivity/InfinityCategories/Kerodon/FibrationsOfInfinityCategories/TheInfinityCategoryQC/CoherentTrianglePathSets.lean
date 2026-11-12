module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePaths

/-!
概要：三角形の三辺と合成 path の具体的な集合表示。
方針：二点の集合を面写像で送り、合成を集合の和として計算する。
規約：単体的圏の標的に依存しない。
使われ方：coherent 三単体の四面の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：二点の標準 path の集合を端点の有限集合として表示する。
方針：標準面写像の像と有限集合の和を計算する。
規約：ULift した対象そのものの集合の等式。
使われ方：三単体の四面の path を同じ四頂点の path と同定する。 -/
lemma coherentOnePath_set : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath.{u}.I = {ULift.up 0, ULift.up 1} := by
  ext k
  rcases k with ⟨k⟩
  fin_cases k <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath]
/-- 概要：三角形の最初の path の集合を端点の有限集合として表示する。
方針：標準面写像の像と有限集合の和を計算する。
規約：ULift した対象そのものの集合の等式。
使われ方：三単体の四面の path を同じ四頂点の path と同定する。 -/
lemma coherentTrianglePath01_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01.{u}.I = {ULift.up 0, ULift.up 1} := by
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath.I = _
  rw [coherentOnePath_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：三角形の後半の path の集合を端点の有限集合として表示する。
方針：標準面写像の像と有限集合の和を計算する。
規約：ULift した対象そのものの集合の等式。
使われ方：三単体の四面の path を同じ四頂点の path と同定する。 -/
lemma coherentTrianglePath12_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12.{u}.I = {ULift.up 1, ULift.up 2} := by
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath.I = _
  rw [coherentOnePath_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：三角形の長辺の path の集合を端点の有限集合として表示する。
方針：標準面写像の像と有限集合の和を計算する。
規約：ULift した対象そのものの集合の等式。
使われ方：三単体の四面の path を同じ四頂点の path と同定する。 -/
lemma coherentTrianglePath02_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02.{u}.I = {ULift.up 0, ULift.up 2} := by
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath.I = _
  rw [coherentOnePath_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：三角形の合成 path の集合を端点の有限集合として表示する。
方針：標準面写像の像と有限集合の和を計算する。
規約：ULift した対象そのものの集合の等式。
使われ方：三単体の四面の path を同じ四頂点の path と同定する。 -/
lemma coherentTriangleCompositePath_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath.{u}.I = {ULift.up 0, ULift.up 1, ULift.up 2} := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01.I ∪ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12.I = _
  rw [coherentTrianglePath01_set, coherentTrianglePath12_set]
  ext k
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
