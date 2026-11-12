module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleComposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTrianglePaths
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

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

/-- 概要：二単体から読み戻した豊穣辺の終点は元の二辺の合成。
方針：Hom 写像の自然性と合成 path の像の式を使う。
規約：元の二つの辺から読み戻した射を合成する。
使われ方：三角形の native な可換性の指定終点の照合。 -/
lemma coherentTriangleHomotopy_target (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).δ 0
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy s) =
      SimplicialCategory.homEquiv' _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 s) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 s)) := by
  have h := ConcreteCategory.congr_hom
    ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋0⦌)
    ((nerve (SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3))
      (ULift.up 2))).δ 0 (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)) = _ at h
  have hs : (nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2))).δ 0
      (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement) =
      ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleCompositePath := (nerve.edgeMk _).tgt_eq
  rw [hs] at h
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleComposite_image s)
/-- 概要：coherent 二単体を長辺と二辺の合成を結ぶ指定された豊穣辺にする。
方針：精密化の像に両端の厳密な等式を添える。
規約：豊穣 Hom の局所 Kan 性は定義に不要。
使われ方：QCat の core Fun の辺と関手同型の読み戻し。 -/
def coherentTriangleEdge (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).Edge
      (SimplicialCategory.homEquiv' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 s)))
      (SimplicialCategory.homEquiv' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 s))) where
  edge := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy s
  src_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy_source s
  tgt_eq := coherentTriangleHomotopy_target s

/-- 概要：通常の順序図式の三角形の豊穣辺は長辺の定値一次単体。
方針：豊穣 Hom の定義を精密化の一次単体で評価する。
規約：恒等に輸送された可換性であることを一単体で記録する。
使われ方：置換後の strict な錐の可換性と指定 path の比較。 -/
lemma coherentTriangleHomotopy_orderDiagram (F : ULift.{u} (Fin 3) ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
        (F.map (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide))))
        1 := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
