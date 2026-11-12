module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronRefinements
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePathSets

/-!
概要：coherent 三単体の長辺を含む二面の path の同定。
方針：三角形の短い path と合成 path の面写像による像を計算する。
規約：有限集合と path の厳密な等式を使う。
使われ方：四面の指定辺を共通の豊穣 Hom の正方形へ揃える。

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

/-- 概要：三角形の長辺の Hom を四頂点の面 013 の長辺の Hom へ送る。
方針：δ₂ の順序写像を path の圏に適用する。
規約：両端は四頂点の 0 と 3。
使われ方：二番目の面の精密化を共通の Hom と同定する。 -/
def coherentTetrahedronFace013 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap _ _
/-- 概要：三角形の長辺の Hom を四頂点の面 023 の長辺の Hom へ送る。
方針：δ₁ の順序写像を path の圏に適用する。
規約：両端は四頂点の 0 と 3。
使われ方：最初の面の精密化を共通の Hom と同定する。 -/
def coherentTetrahedronFace023 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap _ _
/-- 概要：面 013 の長辺 path の像は直接の 03 path。
方針：二点の有限集合の像を計算する。
規約：path 自体の厳密な等式。
使われ方：四面の精密化の始点の同定。 -/
lemma coherentTetrahedronFace013_short :
    coherentTetrahedronFace013.{u}.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath03 := by
  apply SimplicialThickening.Path.ext
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：面 013 の合成 path の像は中間点 1 を含む path。
方針：三点の有限集合の像を計算する。
規約：path 自体の厳密な等式。
使われ方：四面の精密化の中間点の同定。 -/
lemma coherentTetrahedronFace013_long :
    coherentTetrahedronFace013.{u}.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013 := by
  apply SimplicialThickening.Path.ext
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath_set, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：面 023 の長辺 path の像は直接の 03 path。
方針：二点の有限集合の像を計算する。
規約：path 自体の厳密な等式。
使われ方：四面の精密化の始点の同定。 -/
lemma coherentTetrahedronFace023_short :
    coherentTetrahedronFace023.{u}.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath03 := by
  apply SimplicialThickening.Path.ext
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02_set, Set.image_insert_eq, Set.image_singleton]
  rfl
/-- 概要：面 023 の合成 path の像は中間点 2 を含む path。
方針：三点の有限集合の像を計算する。
規約：path 自体の厳密な等式。
使われ方：四面の精密化の中間点の同定。 -/
lemma coherentTetrahedronFace023_long :
    coherentTetrahedronFace023.{u}.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023 := by
  apply SimplicialThickening.Path.ext
  change _ '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath.I = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath_set, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
