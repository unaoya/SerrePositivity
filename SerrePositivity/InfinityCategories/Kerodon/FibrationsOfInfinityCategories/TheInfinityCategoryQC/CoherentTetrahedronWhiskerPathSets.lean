module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronWhiskerFunctors

/-!
概要：三単体の左右合成による四つの path の同定。
方針：四頂点の path の合成を有限集合の和集合として計算する。
規約：両端と精密化の一次単体を厳密に保つ。
使われ方：coherent 三単体の四面の合成則。

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

/-- 概要：固定した 01 path の二点集合の表示。
方針：二点の像を計算する。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronPath01_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01.{u}.I = {ULift.up 0, ULift.up 1} := by
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：固定した 23 path の二点集合の表示。
方針：二点の像を計算する。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronPath23_set :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23.{u}.I = {ULift.up 2, ULift.up 3} := by
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：面 123 の長辺への前合成は 013 path。
方針：有限集合の和集合を計算する。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronWhisker013_short :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace123.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronWhisker01).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013 := by
  apply SimplicialThickening.Path.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01.I ∪ (_ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02.I) = _
  rw [coherentTetrahedronPath01_set, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02_set,
    Set.image_insert_eq, Set.image_singleton]
  ext k
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
/-- 概要：面 123 の合成 path への前合成は全四点の path。
方針：四つの頂点を場合分けする。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronWhisker013_long :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace123.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronWhisker01).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123 := by
  apply SimplicialThickening.Path.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01.I ∪ (_ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath.I) = _
  rw [coherentTetrahedronPath01_set, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath_set,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  ext k
  rcases k with ⟨k⟩
  fin_cases k <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath] <;> decide
/-- 概要：面 012 の長辺への後合成は 023 path。
方針：有限集合の和集合を計算する。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronWhisker023_short :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace012.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronWhisker23).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023 := by
  apply SimplicialThickening.Path.ext
  change (_ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02.I) ∪ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02_set, coherentTetrahedronPath23_set,
    Set.image_insert_eq, Set.image_singleton]
  ext k
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
/-- 概要：面 012 の合成 path への後合成は全四点の path。
方針：四つの頂点を場合分けする。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
lemma coherentTetrahedronWhisker023_long :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace012.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronWhisker23).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123 := by
  apply SimplicialThickening.Path.ext
  change (_ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath.I) ∪ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath_set, coherentTetrahedronPath23_set,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  ext k
  rcases k with ⟨k⟩
  fin_cases k <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath] <;> decide

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
