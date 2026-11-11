module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronEndEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorWhiskerSimplex

/-!
概要：𝒮 の三単体の四面の円柱を元の三角形と前後合成へ厳密に同定する。
方針：豊穣精密化の面の式と Kan 豊穣構造の内部 Hom 表示。
規約：ホモトピー類だけでなく全一単体を保つ。使われ方：指定 path の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 013 は元の三角形の辺そのもの。
方針：豊穣 Hom の面の式。規約：全一単体。使われ方：正方形の第一辺。 -/
lemma spaceTetrahedron_face_two (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013).edge =
      (spaceInfinityTriangleEdge (SpaceInfinity.δ 2 s)).edge :=
  (coherentTetrahedronHom_face_two s).symm

/-- 概要：面 023 は元の三角形の辺そのもの。
方針：豊穣 Hom の面の式。規約：全一単体。使われ方：正方形の第三辺。 -/
lemma spaceTetrahedron_face_one (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023).edge =
      (spaceInfinityTriangleEdge (SpaceInfinity.δ 1 s)).edge :=
  (coherentTetrahedronHom_face_one s).symm

/-- 概要：面 123 の前合成は元の第二精密化の辺。
方針：豊穣合成の式と内部 Hom の前合成を比較。
規約：元の関手 01。使われ方：指定四面の合成則。 -/
lemma spaceTetrahedron_face_zero (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).edge =
      ((pre (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
        coherentEdgeHom (SpaceInfinity.δ 2 (SpaceInfinity.δ 2 s)))).app
          (s.obj ⟨ULift.up 3⟩).obj).app (Opposite.op ⦋1⦌)
            (spaceInfinityTriangleEdge (SpaceInfinity.δ 0 s)).edge := by
  have h := coherentTetrahedronHom_face_zero s
  rw [coherentTetrahedronPath01_image, kanHom_vertex] at h
  exact h.trans (functorPrecomposition_simplex _ 1 _)

/-- 概要：面 012 の後合成は元の第四精密化の辺。
方針：豊穣合成の式と内部 Hom の後合成を比較。
規約：元の関手 23。使われ方：指定四面の合成則。 -/
lemma spaceTetrahedron_face_three (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).edge =
      ((ihom (s.obj ⟨ULift.up 0⟩).obj).map
        (show (s.obj ⟨ULift.up 2⟩).obj ⟶ (s.obj ⟨ULift.up 3⟩).obj from
          coherentEdgeHom (SpaceInfinity.δ 0 (SpaceInfinity.δ 1 s)))).app (Opposite.op ⦋1⦌)
            (spaceInfinityTriangleEdge (SpaceInfinity.δ 3 s)).edge := by
  have h := coherentTetrahedronHom_face_three s
  rw [coherentTetrahedronPath23_image, kanHom_vertex] at h
  exact h.trans (functorPostcomposition_simplex _ 1 _)

end SerrePositivity.InfinityCategories.F2
