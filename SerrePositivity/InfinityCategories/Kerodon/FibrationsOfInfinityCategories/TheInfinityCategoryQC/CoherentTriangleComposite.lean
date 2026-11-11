module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePaths

/-!
概要：任意の coherent 二単体から指定された豊穣 Hom の辺を読み戻す。
方針：長辺の path から合成 path への精密化の像を取る。
規約：対象と Hom の宇宙を分け、Hom の宇宙を u とする。
使われ方：Cat_∞ の錐の native な三角形と指定 path の比較。

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

/-- 概要：二辺の合成 path の像は読み戻した通常の二射の合成の豊穣頂点。
方針：豊穣合成の零単体と通常の射の全単射を合わせる。
規約：射を同値な別の代表へ変更しない。
使われ方：native な三角形の指定された合成側の端点の照合。 -/
lemma coherentTriangleComposite_image (s : (SimplicialNerve C) _⦋2⦌) :
    (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath) =
      SimplicialCategory.homEquiv' _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 s) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 s)) := by
  let a : SimplicialThickening (ULift.{u} (Fin 3)) := ⟨ULift.up 0⟩
  let b : SimplicialThickening (ULift.{u} (Fin 3)) := ⟨ULift.up 1⟩
  let c : SimplicialThickening (ULift.{u} (Fin 3)) := ⟨ULift.up 2⟩
  let x : (SimplicialCategory.sHom a b) _⦋0⦌ :=
    ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01
  let y : (SimplicialCategory.sHom b c) _⦋0⦌ :=
    ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12
  have h := congrArg
    (fun m : (SimplicialCategory.sHom a b ⊗ SimplicialCategory.sHom b c) ⟶
      SimplicialCategory.sHom (s.obj a) (s.obj c) ↦ m.app (Opposite.op ⦋0⦌) (x, y))
    (s.map_comp a b c)
  have hc : (eComp SSet a b c).app (Opposite.op ⦋0⦌) (x, y) =
      ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath := by
    apply ComposableArrows.ext₀
    rfl
  change (s.map a c).app (Opposite.op ⦋0⦌)
      ((eComp SSet a b c).app (Opposite.op ⦋0⦌) (x, y)) =
    (eComp SSet (s.obj a) (s.obj b) (s.obj c)).app (Opposite.op ⦋0⦌)
      ((s.map a b).app (Opposite.op ⦋0⦌) x, (s.map b c).app (Opposite.op ⦋0⦌) y) at h
  rw [hc] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp]
  refine h.trans ?_
  apply congrArg ((eComp SSet (s.obj a) (s.obj b) (s.obj c)).app (Opposite.op ⦋0⦌))
  apply Prod.ext
  · exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm
  · exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
