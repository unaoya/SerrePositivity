module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SpecifiedSimplexEdge

/-!
概要：指定関手同型の両端の射の等式による輸送。
方針：関手の等式を消去し、元の同型をそのまま使う。
規約：順方向の射と指定辺の類の対応を保つ。
使われ方：四面の関手同型を共通の六関手で表す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：両端の関手を等しい関手に置き換えた指定同型。
方針：二つの射の等式を消去する。
規約：別の同型を選択しない。
使われ方：三角形の同型の端点を共通の境界関手に揃える。 -/
def functorIsoOfEq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g' := by
  subst f' g'
  exact e

/-- 概要：両端を輸送しても元の指定関手同型と型を含めて等しい。
方針：二つの端点の関手の等式を消去する。
規約：指定同型の値を保持する。
使われ方：四面の指定同型の共通の境界への移行。 -/
lemma functorIsoOfEq_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') :
    HEq (functorIsoOfEq e hf hg) e := by
  subst f' g'
  rfl

/-- 概要：射の等式による輸送は指定辺の類との対応を保つ。
方針：関手の等式を消去し、元の類との一致を使う。
規約：辺の代表を変更せず両端だけを輸送する。
使われ方：輸送した三角形の同型の合成則を指定辺の正方形へ戻す。 -/
lemma functorIsoOfEq_hom {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (t : ((ihom X).obj Y).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    (h : e.hom = SSet.Truncated.HomotopyCategory.homMk t.toTruncated) :
    (functorIsoOfEq e hf hg).hom = SSet.Truncated.HomotopyCategory.homMk
      (t.ofEq (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hg)).toTruncated := by
  subst f' g'
  exact h

/-- 概要：輸送した関手同型の射は明示した一次単体の辺の類。
方針：両端だけの輸送と指定一次単体への置換の類の一致を合わせる。
規約：元の指定同型と元の一次単体を保持する。
使われ方：四面の同型と正方形の辺の類の照合。 -/
lemma functorIsoOfEq_hom_simplex {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (t : ((ihom X).obj Y).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    (r : ((ihom X).obj Y) _⦋1⦌) (hr : r = t.edge)
    (h : e.hom = SSet.Truncated.HomotopyCategory.homMk t.toTruncated) :
    (functorIsoOfEq e hf hg).hom = SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeOfSimplexWithEndpoints t r hr
        (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hg)).toTruncated :=
  (functorIsoOfEq_hom e hf hg t h).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeOfSimplexWithEndpoints_homMk _ _ _ _ _).symm

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
