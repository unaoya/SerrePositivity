module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronWhiskerChains

/-!
概要：面 δ₀ の指定辺と始端の射の合成。
方針：精密化の像と豊穣関手の合成の保存を一次単体で照合する。
規約：元の一単体を別の代表へ変更しない。
使われ方：Cat_∞ の三単体の四面の指定関手同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：面 δ₀ の指定辺を 01 と合成すると 013 から全 path への辺。
方針：豊穣合成の一次単体と定値単体への自然性を使う。
規約：元の一単体の厳密な等式。
使われ方：四面の合成則を同じ Hom で比較する。 -/
lemma coherentTetrahedronHom_face_zero (s : (SimplicialNerve C) _⦋3⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013Full).edge =
      (eComp SSet (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 1⟩) (s.obj ⟨ULift.up 3⟩)).app
        (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app
          (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01)) 1,
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy ((SimplicialNerve C).δ 0 s)) := by
  let a : SimplicialThickening (ULift.{u} (Fin 4)) := ⟨ULift.up 0⟩
  let b : SimplicialThickening (ULift.{u} (Fin 4)) := ⟨ULift.up 1⟩
  let c : SimplicialThickening (ULift.{u} (Fin 4)) := ⟨ULift.up 3⟩
  let x : (SimplicialCategory.sHom a b) _⦋1⦌ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01) 1
  let y : (SimplicialCategory.sHom b c) _⦋1⦌ :=
    (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace123).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)
  have h := congrArg
    (fun m : (SimplicialCategory.sHom a b ⊗ SimplicialCategory.sHom b c) ⟶
      SimplicialCategory.sHom (s.obj a) (s.obj c) ↦ m.app (Opposite.op ⦋1⦌) (x, y))
    (s.map_comp a b c)
  have hc : (eComp SSet a b c).app (Opposite.op ⦋1⦌) (x, y) =
      ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013Full := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronWhisker013_chain]
    apply ComposableArrows.ext₁ rfl rfl
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
  change (s.map a c).app (Opposite.op ⦋1⦌)
      ((eComp SSet a b c).app (Opposite.op ⦋1⦌) (x, y)) =
    (eComp SSet (s.obj a) (s.obj b) (s.obj c)).app (Opposite.op ⦋1⦌)
      ((s.map a b).app (Opposite.op ⦋1⦌) x, (s.map b c).app (Opposite.op ⦋1⦌) y) at h
  rw [hc] at h
  rw [show (s.map a b).app (Opposite.op ⦋1⦌) x =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((s.map a b).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01)) 1 from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map _ _ _] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
