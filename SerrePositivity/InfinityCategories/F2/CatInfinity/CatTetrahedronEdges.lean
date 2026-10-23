module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoherentTetrahedronEndEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleIso

/-!
概要：三単体の四面の関手空間内での合成の一致。
方針：path の像と豊穣 Hom から core Fun への包含を計算する。
規約：元の一単体とそのホモトピー類を保持する。
使われ方：Cat_∞ の引き戻し錐の指定可換性の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三単体の精密化を関手空間の指定辺にする。
方針：豊穣 Hom の辺を core Fun の包含で送る。
規約：元の辺の代表を保つ。
使われ方：四面の指定関手同型の合成則。 -/
def catInfinityTetrahedronEdge (s : CatInfinity.{u} _⦋3⦌)
    {P Q : SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)}
    (r : P ⟶ Q) :=
  (coherentTetrahedronHomEdge s r).map
    (quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj)).ι
/-- 概要：四面の精密化の像の合成は関手空間で一致。
方針：豊穣 Hom の正方形を包含が誘導する関手で送る。
規約：元の辺の代表を保つ。
使われ方：四面の指定関手同型の合成則。 -/
lemma catInfinityTetrahedron_square (s : CatInfinity.{u} _⦋3⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronEdge s coherentTetrahedronRefine013).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronEdge s coherentTetrahedronRefine013Full).toTruncated =
    SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronEdge s coherentTetrahedronRefine023).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk
        (catInfinityTetrahedronEdge s coherentTetrahedronRefine023Full).toTruncated := by
  let F := SSet.mapHomotopyCategory
    (quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj)).ι
  have h := congrArg F.map (coherentTetrahedronHom_square s)
  rw [F.map_comp, F.map_comp] at h
  exact h
/-- 概要：面 δ₂ の指定辺は 03 から 013 への辺。
方針：豊穣 Hom での面の一致を包含で送る。
規約：元の辺の代表を保つ。
使われ方：四面の指定関手同型の合成則。 -/
lemma catInfinityTetrahedron_face_two (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine013).edge =
      (catInfinityTriangleEdge (CatInfinity.δ 2 s)).edge := by
  exact congrArg
    ((quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋1⦌))
    (coherentTetrahedronHom_face_two s).symm
/-- 概要：面 δ₁ の指定辺は 03 から 023 への辺。
方針：豊穣 Hom での面の一致を包含で送る。
規約：元の辺の代表を保つ。
使われ方：四面の指定関手同型の合成則。 -/
lemma catInfinityTetrahedron_face_one (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine023).edge =
      (catInfinityTriangleEdge (CatInfinity.δ 1 s)).edge := by
  exact congrArg
    ((quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋1⦌))
    (coherentTetrahedronHom_face_one s).symm

end SerrePositivity.InfinityCategories.F2
