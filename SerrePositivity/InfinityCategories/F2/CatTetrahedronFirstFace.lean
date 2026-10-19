module

public import SerrePositivity.InfinityCategories.F2.CatTetrahedronEdges

/-!
概要：面 δ₀ の関手の辺に元の辺 01 を前合成する式。
方針：豊穣 Hom の合成と core の包含を関手空間の合成へ移す。
規約：固定射も三角形の辺も元の三単体から読み戻す。
使われ方：Cat_∞ の四面の合成則と引き戻し錐の可換性の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 δ₀ の関手の辺に元の辺 01 を前合成する式。
方針：包含が豊穣合成を保つ式を一次単体で評価する。
規約：指定された三角形の一単体との厳密な等式。
使われ方：四面の合成関係の二番目の辺を関手の合成で表示する。 -/
lemma catInfinityTetrahedron_face_zero (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine013Full).edge =
      (MonoidalClosed.comp (s.obj ⟨ULift.up 0⟩).obj
        (s.obj ⟨ULift.up 1⟩).obj (s.obj ⟨ULift.up 3⟩).obj).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant
          (functorVertex (coherentEdgeHom (CatInfinity.δ 2 (CatInfinity.δ 2 s)))) 1,
          (catInfinityTriangleEdge (CatInfinity.δ 0 s)).edge) := by
  have hv : (quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 1⟩).obj)).ι.app (Opposite.op ⦋0⦌)
        ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentTetrahedronPath01)) =
      functorVertex (coherentEdgeHom (CatInfinity.δ 2 (CatInfinity.δ 2 s))) :=
    (congrArg ((quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 1⟩).obj)).ι.app (Opposite.op ⦋0⦌))
        (coherentTetrahedronPath01_image s)).trans (qCatHom_vertex_ι _ _ _)
  have h := congrArg
    ((quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋1⦌))
    (coherentTetrahedronHom_face_zero s)
  have hc := congrArg (fun m ↦ m.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ coherentTetrahedronPath01)) 1,
      coherentTriangleHomotopy (CatInfinity.δ 0 s)))
    (qCatHom_comp_ι (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 1⟩) (s.obj ⟨ULift.up 3⟩))
  refine h.trans (hc.trans ?_)
  change (MonoidalClosed.comp (s.obj ⟨ULift.up 0⟩).obj
    (s.obj ⟨ULift.up 1⟩).obj (s.obj ⟨ULift.up 3⟩).obj).app (Opposite.op ⦋1⦌)
      ((quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
        (s.obj ⟨ULift.up 1⟩).obj)).ι.app (Opposite.op ⦋1⦌)
          (PinchedHom.constant _ 1), _) = _
  rw [pinchedConstant_map, hv]
  rfl

end SerrePositivity.InfinityCategories.F2
