module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTriangleIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.StrictNativeConeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedra

/-!
概要：定値な豊穣辺を持つ coherent 三角形の判定。
方針：通常の nerve から来る三角形の辺と端点を計算する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：coherent 三角形の豊穣 Hom の辺が定値である条件。
方針：定値辺を与える零単体の存在で定義する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
def IsConstantCoherentTriangle {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) : Prop :=
  ∃ x : (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1
/-- 概要：通常の nerve に由来する三角形の定値性。
方針：順序図式の三角形の豊穣辺の計算を使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isConstantCoherentTriangle_nerve {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (nerve C) _⦋2⦌) :
    IsConstantCoherentTriangle ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) s) := by
  exact ⟨_, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy_orderDiagram _⟩
/-- 概要：strict な錐の三角形の定値性。
方針：通常の nerve を経由する表示へ戻す。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isConstantCoherentTriangle_strictCone {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C} (c : Cone F)
    (k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋1⦌) :
    IsConstantCoherentTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle, SSet.yonedaEquiv_comp]
  change IsConstantCoherentTriangle ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) _)
  exact isConstantCoherentTriangle_nerve _
/-- 概要：定値な豊穣辺の値は長辺に対応する零単体。
方針：始点面を取り定値辺の値を同定する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma coherentTriangleHomotopy_constant_source {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (s : (SimplicialNerve C) _⦋2⦌) (hs : IsConstantCoherentTriangle s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (SimplicialCategory.homEquiv' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 s))) 1 := by
  rcases hs with ⟨x, hx⟩
  let H := SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
  have hδ : H.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = x := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact (SSet.Truncated.Edge.id (X := (truncation 2).obj H) x).src_eq
  have hv := hδ.symm.trans ((congrArg (H.δ 1) hx).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy_source s))
  exact hx.trans (congrArg (fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1) hv)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
