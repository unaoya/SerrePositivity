module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition

/-!
概要：指定全比較の二回の制限を元合成包含への制限へ照合する。
方針：前合成関手と同じ全関手同型の値を使う。
規約：元の比較を選び直さない。使われ方：元二胞体から指定短辺全比較の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories
open scoped _root_.Simplicial
/-- 概要：指定全比較の二回の制限は合成包含への制限と一致する。
方針：前合成とホモトピー圏の関手性を使う。規約：元同型の値を保持。
使われ方：元二胞体を経由した短辺比較の回収。 -/
lemma specifiedFunctorIsoRestrictionTwice {A B C X : SSet.{u}} {f g : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : B ⟶ A) (q : C ⟶ B) :
    HEq ((e.precomp p).precomp q) (e.precomp (q ≫ p)) := by
  have h : SSet.mapHomotopyCategory ((pre (q ≫ p)).app X) =
      SSet.mapHomotopyCategory ((pre p).app X) ⋙
        SSet.mapHomotopyCategory ((pre q).app X) := by
    change (hoFunctor.map ((pre (q ≫ p)).app X)).toFunctor = _
    rw [pre_map]
    change (hoFunctor.map ((pre p).app X ≫ (pre q).app X)).toFunctor = _
    rw [CategoryTheory.Functor.map_comp]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq h e).symm

/-- 概要：元二胞体と元短辺の厳密回収から元全比較の短辺を回収する。
方針：同じ元二回の制限と指定同型の値を照合する。規約：全指定同型を保持。
使われ方：全右面の指定三境界への接続。 -/
lemma specifiedFunctorIsoRestrictionFromTriangle {A B C X : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ X} {f'' g'' : C ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : B ⟶ A) (q : C ⟶ B) (s : C ⟶ A)
    (hp : q ≫ p = s) (hf : p ≫ f = f') (hg : p ≫ g = g')
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (htri : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.precomp p) hf hg = e')
    (hfs : q ≫ f' = f'') (hgs : q ≫ g' = g'')
    (e'' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f'' g'')
    (hshort : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e'.precomp q) hfs hgs = e'') :
    HEq (e.precomp s) e'' := by
  subst f' g'
  change e.precomp p = e' at htri
  subst e'
  have ht := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.specifiedFunctorIsoRestrictionTwice e p q
  rw [hp] at ht
  exact ht.symm.trans ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ hfs hgs).symm.trans (heq_of_eq hshort))

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
