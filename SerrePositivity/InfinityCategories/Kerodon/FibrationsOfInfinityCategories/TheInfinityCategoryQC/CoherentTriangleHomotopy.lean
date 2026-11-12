module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData
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
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：coherent 二単体を長辺から二辺の合成への豊穣 Hom の一単体へ送る。
方針：標準 path の精密化を豊穣 Hom の写像で評価する。
規約：任意の単体的圏を扱い、局所 Kan 性は不要。
使われ方：Cat_∞ の native な三角形の可換関手同型の読み戻し。 -/
def coherentTriangleHomotopy (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) _⦋1⦌ :=
  (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)
/-- 概要：二単体から読み戻した豊穣辺の始点は長辺の指定射。
方針：Hom 写像の自然性と辺の零単体での読み戻しを使う。
規約：元の長辺の射を厳密に保持する。
使われ方：native な三角形の可換性の方向と始点の照合。 -/
lemma coherentTriangleHomotopy_source (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).δ 1
        (coherentTriangleHomotopy s) =
      SimplicialCategory.homEquiv' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 s)) := by
  change _ = (SimplicialCategory.homEquiv' _ _)
    ((SimplicialCategory.homEquiv' _ _).symm
      ((((SimplicialNerve C).δ 1 s).map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app
        (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)))
  rw [Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom
    ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).naturality (SimplexCategory.δ (1 : Fin 2)).op)
    (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋0⦌)
    ((nerve (SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
      (ULift.up 2))).δ 1 (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)) = _ at h
  have hs : (nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2))).δ 1
      (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement) =
      ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath02 := (nerve.edgeMk _).src_eq
  rw [hs] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
