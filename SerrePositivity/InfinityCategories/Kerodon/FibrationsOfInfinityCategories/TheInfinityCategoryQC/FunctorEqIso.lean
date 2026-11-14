module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：関手の等式から来る指定同型の判定。
方針：定値な代表辺をホモトピー圏の恒等射へ戻す。
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

/-- 概要：関手の等式から標準関手同型を作る。
方針：始域の恒等同型の終点を等式で輸送する。
規約：新たな辺の代表を選択しない。
使われ方：strict な三角形の簡約結果を表す。 -/
def functorEqIso {X Y : SSet.{u}} {f g : X ⟶ Y} (h : f = g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f from Iso.refl _) rfl h

/-- 概要：指定関手同型が関手の等式から来る条件。
方針：恒等同型の端点を等式で輸送した値との一致で定義する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
def IsFunctorEqIso {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : Prop :=
  ∃ h : f = g, e = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f from Iso.refl _) rfl h
/-- 概要：定値辺を代表とする指定同型は等式から来る。
方針：終点を始点と同定し辺の類を恒等射へ戻す。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isFunctorEqIso_of_constant_edge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (t : ((ihom X).obj Y).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    (hh : e.hom = SSet.Truncated.HomotopyCategory.homMk t.toTruncated)
    (ht : t.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) 1) : IsFunctorEqIso e := by
  have hδ : ((ihom X).obj Y).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom X).obj Y)) _).tgt_eq
  have hg : g = f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    (t.tgt_eq.symm.trans ((congrArg (((ihom X).obj Y).δ 0) ht).trans hδ))
  subst g
  refine ⟨rfl, ?_⟩
  change e = Iso.refl _
  apply Iso.ext
  rw [hh]
  have he : t.toTruncated =
      SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom X).obj Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
    apply SSet.Truncated.Edge.ext
    exact ht.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
  rw [he, SSet.Truncated.HomotopyCategory.homMk_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
