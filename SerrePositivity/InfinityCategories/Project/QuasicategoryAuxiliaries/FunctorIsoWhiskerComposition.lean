module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit

/-!
概要：指定関手同型の後合成の結合と前後合成の交換。
方針：内部 Hom とホモトピー圏の関手性を使う。
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
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：指定関手同型の前後合成は内部 Hom の合成則に従う。
方針：ホモトピー圏の誘導関手を同定して mapIso に作用させる。
規約：元の同型の値と合成の順を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma functorIso_postcomp_postcomp {W X Y Z : SSet.{u}} {f g : W ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : X ⟶ Y) (q : Y ⟶ Z) :
    (e.postcomp p).postcomp q = e.postcomp (p ≫ q) := by
  have h : SSet.mapHomotopyCategory ((ihom W).map (p ≫ q)) =
      SSet.mapHomotopyCategory ((ihom W).map p) ⋙
        SSet.mapHomotopyCategory ((ihom W).map q) := by
    change (hoFunctor.map ((ihom W).map (p ≫ q))).toFunctor = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
  exact (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq h e)).symm
/-- 概要：指定関手同型の前後合成は内部 Hom の合成則に従う。
方針：ホモトピー圏の誘導関手を同定して mapIso に作用させる。
規約：元の同型の値と合成の順を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma functorIso_precomp_postcomp {W X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : W ⟶ X) (q : Y ⟶ Z) :
    (e.precomp p).postcomp q = (e.postcomp q).precomp p := by
  have h : SSet.mapHomotopyCategory ((pre p).app Y) ⋙
      SSet.mapHomotopyCategory ((ihom W).map q) =
    SSet.mapHomotopyCategory ((ihom X).map q) ⋙
      SSet.mapHomotopyCategory ((pre p).app Z) := by
    change (hoFunctor.map ((pre p).app Y)).toFunctor ⋙
        (hoFunctor.map ((ihom W).map q)).toFunctor = _
    have hn := congrArg (fun m ↦ (hoFunctor.map m).toFunctor) ((pre p).naturality q)
    simpa only [CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor] using! hn.symm
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq h e)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
