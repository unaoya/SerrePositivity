module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso


/-!
概要：関手の等式から来る同型の演算による保存。
方針：等式の消去とホモトピー圏の mapIso を使う。
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

/-- 概要：等式から来る同型は任意の等式証明による標準同型と一致。
方針：等式証明の proof irrelevance を使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma IsFunctorEqIso.eq {X Y : SSet.{u}} {f g : X ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) (h : f = g) :
    e = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f from Iso.refl _) rfl h := by
  rcases he with ⟨h', he⟩
  exact he
/-- 概要：等式から来る同型の逆も等式から来る。
方針：端点の等式を消去して恒等同型に戻す。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma IsFunctorEqIso.symm {X Y : SSet.{u}} {f g : X ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e.symm := by
  rcases he with ⟨h, he⟩
  subst g
  subst e
  exact ⟨rfl, rfl⟩
/-- 概要：等式から来る同型の合成も等式から来る。
方針：二つの端点等式を消去して恒等同型を合成する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma IsFunctorEqIso.trans {X Y : SSet.{u}} {f g h : X ⟶ Y}
    {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso d) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (e ≪≫ d) := by
  rcases he with ⟨hfg, he⟩
  rcases hd with ⟨hgh, hd⟩
  subst g
  subst h
  subst e
  subst d
  exact ⟨rfl, Iso.refl_trans _⟩
/-- 概要：等式から来る同型は前合成で保たれる。
方針：ホモトピー圏の関手が恒等同型を保つことを使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma IsFunctorEqIso.precomp {W X Y : SSet.{u}} {f g : X ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) (q : W ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (e.precomp q) := by
  rcases he with ⟨h, he⟩
  subst g
  subst e
  refine ⟨rfl, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact Functor.mapIso_refl _ _
/-- 概要：等式から来る同型は後合成で保たれる。
方針：ホモトピー圏の関手が恒等同型を保つことを使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma IsFunctorEqIso.postcomp {X Y Z : SSet.{u}} {f g : X ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) (q : Y ⟶ Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (e.postcomp q) := by
  rcases he with ⟨h, he⟩
  subst g
  subst e
  refine ⟨rfl, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
  exact Functor.mapIso_refl _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
