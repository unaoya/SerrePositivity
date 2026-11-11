module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTetrahedronFirstFace

/-!
概要：面 δ₃ の関手の辺に元の辺 23 を後合成する式。
方針：豊穣 Hom の合成と core の包含を関手空間の合成へ移す。
規約：固定射も三角形の辺も元の三単体から読み戻す。
使われ方：Cat_∞ の四面の合成則と引き戻し錐の可換性の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：面 δ₃ の関手の辺に元の辺 23 を後合成する式。
方針：包含が豊穣合成を保つ式を一次単体で評価する。
規約：指定された三角形の一単体との厳密な等式。
使われ方：四面の合成関係の二番目の辺を関手の合成で表示する。 -/
lemma catInfinityTetrahedron_face_three (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTetrahedronEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine023Full).edge =
      (MonoidalClosed.comp (s.obj ⟨ULift.up 0⟩).obj
        (s.obj ⟨ULift.up 2⟩).obj (s.obj ⟨ULift.up 3⟩).obj).app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 3 s)).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 s)))) 1) := by
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 2⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋0⦌)
        ((s.map ⟨ULift.up 2⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 s))) :=
    (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 2⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋0⦌))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23_image s)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_vertex_ι _ _ _)
  have h := congrArg
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
      (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronHom_face_three s)
  have hc := congrArg (fun m ↦ m.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 3 s),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((s.map ⟨ULift.up 2⟩ ⟨ULift.up 3⟩).app
        (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23)) 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_comp_ι (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩) (s.obj ⟨ULift.up 3⟩))
  refine h.trans (hc.trans ?_)
  change (MonoidalClosed.comp (s.obj ⟨ULift.up 0⟩).obj
    (s.obj ⟨ULift.up 2⟩).obj (s.obj ⟨ULift.up 3⟩).obj).app (Opposite.op ⦋1⦌)
      (_, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 2⟩).obj).obj
        (s.obj ⟨ULift.up 3⟩).obj)).ι.app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _ 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, hv]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
