module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso

/-!
概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
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

/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_comp {K L M : SSet.{u}} {x y : K _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (f : K ⟶ L) (g : L ⟶ M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f) g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (f ≫ g) := by
  have h : (hoFunctor.map f).toFunctor ⋙ (hoFunctor.map g).toFunctor =
      (hoFunctor.map (f ≫ g)).toFunctor := by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq h e)
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_heq {K L : SSet.{u}} {x y : K _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) {f g : K ⟶ L} (h : f = g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e g) := by
  cases h
  rfl
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma functorEqIso_eqToIso {X Y : SSet.{u}} {f g : X ⟶ Y} (h : f = g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso h = eqToIso (congrArg SSet.HomotopyCategory.mk (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)) := by
  subst g
  rfl
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_eqToIso_of_terminal {K L : SSet.{u}} [Quasicategory L]
    {x y : K _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (f : K ⟶ L)
    (h : f.app (Opposite.op ⦋0⦌) x = f.app (Opposite.op ⦋0⦌) y)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (f.app (Opposite.op ⦋0⦌) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f = eqToIso (congrArg SSet.HomotopyCategory.mk h) := by
  apply Iso.ext
  exact ht.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
