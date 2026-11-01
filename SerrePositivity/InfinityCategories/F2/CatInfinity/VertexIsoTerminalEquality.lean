module

public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIso
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace

/-!
概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_comp {K L M : SSet.{u}} {x y : K _⦋0⦌}
    (e : VertexIso x y) (f : K ⟶ L) (g : L ⟶ M) :
    VertexIso.map (VertexIso.map e f) g = VertexIso.map e (f ≫ g) := by
  have h : (hoFunctor.map f).toFunctor ⋙ (hoFunctor.map g).toFunctor =
      (hoFunctor.map (f ≫ g)).toFunctor := by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  exact eq_of_heq (mapIso_heq_of_functor_eq h e)
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_heq {K L : SSet.{u}} {x y : K _⦋0⦌}
    (e : VertexIso x y) {f g : K ⟶ L} (h : f = g) :
    HEq (VertexIso.map e f) (VertexIso.map e g) := by
  cases h
  rfl
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma functorEqIso_eqToIso {X Y : SSet.{u}} {f g : X ⟶ Y} (h : f = g) :
    functorEqIso h = eqToIso (congrArg SSet.HomotopyCategory.mk (congrArg functorVertex h)) := by
  subst g
  rfl
/-- 概要：頂点の指定同型の輸送と終頂点での一意性。
方針：ホモトピー圏の関手性と終対象への射の一意性を使う。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma vertexIso_map_eqToIso_of_terminal {K L : SSet.{u}} [Quasicategory L]
    {x y : K _⦋0⦌} (e : VertexIso x y) (f : K ⟶ L)
    (h : f.app (Opposite.op ⦋0⦌) x = f.app (Opposite.op ⦋0⦌) y)
    (ht : IsTerminalVertex (f.app (Opposite.op ⦋0⦌) y)) :
    VertexIso.map e f = eqToIso (congrArg SSet.HomotopyCategory.mk h) := by
  apply Iso.ext
  exact ht.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2
