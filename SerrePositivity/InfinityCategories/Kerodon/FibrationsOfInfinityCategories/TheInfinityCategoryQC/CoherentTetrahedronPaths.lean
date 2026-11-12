module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePaths

/-!
概要：coherent 三単体の四面を同じ Hom へ移す四つの path。
方針：両端と選んだ中間点を有限集合で指定する。
規約：対象は ULift (Fin 4)。
使われ方：四面の指定関手同型の合成則。

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

/-- 概要：四頂点中の両端を含む集合を 0 から 3 への path にする。
方針：両端の所属と四点順序の最小・最大を使う。
規約：中間点の有無は入力の集合で指定する。
使われ方：三単体の二通りの精密化の四つの頂点。 -/
def coherentFourPath (S : Set (ULift.{u} (Fin 4)))
    (h₀ : ULift.up (0 : Fin 4) ∈ S) (h₃ : ULift.up (3 : Fin 4) ∈ S) :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  I := S
  left := h₀
  right := h₃
  left_le k _ := Fin.zero_le k.down
  le_right k _ := Fin.le_last k.down
/-- 概要：両端のみ を含む四点の path。
方針：指定した有限集合を両端を持つ path にする。
規約：両端は 0 と 3。
使われ方：三単体の四面の合成則の共通の豊穣 Hom。 -/
def coherentTetrahedronPath03 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  coherentFourPath {ULift.up 0, ULift.up 3} (by simp) (by simp)
/-- 概要：中間点 1 を含む四点の path。
方針：指定した有限集合を両端を持つ path にする。
規約：両端は 0 と 3。
使われ方：三単体の四面の合成則の共通の豊穣 Hom。 -/
def coherentTetrahedronPath013 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  coherentFourPath {ULift.up 0, ULift.up 1, ULift.up 3} (by simp) (by simp)
/-- 概要：中間点 2 を含む四点の path。
方針：指定した有限集合を両端を持つ path にする。
規約：両端は 0 と 3。
使われ方：三単体の四面の合成則の共通の豊穣 Hom。 -/
def coherentTetrahedronPath023 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  coherentFourPath {ULift.up 0, ULift.up 2, ULift.up 3} (by simp) (by simp)
/-- 概要：四頂点全て を含む四点の path。
方針：指定した有限集合を両端を持つ path にする。
規約：両端は 0 と 3。
使われ方：三単体の四面の合成則の共通の豊穣 Hom。 -/
def coherentTetrahedronPath0123 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  coherentFourPath Set.univ (by simp) (by simp)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
