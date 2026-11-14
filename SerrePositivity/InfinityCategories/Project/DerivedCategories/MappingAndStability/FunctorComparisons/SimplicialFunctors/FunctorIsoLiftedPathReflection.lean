module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomTwoThreeTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyRawTransport
/-!
概要：同じ指定五角経路の二辺・三辺等式を、完全充満な後合成から反映する。
方針：各端点と指定同型の異種等式を射へ移し、全関手射の単射性を使う。
規約：元の指定値を保つ。使われ方：通常 kernel から K-flat の五角式への移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 完全充満な実包含後の同じ指定五角経路の等式を、元の全関手同型へ反映する。 -/
lemma functorIso_two_three_reflect_postcomp {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (i : Y ⟶ Z) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    {f g h t k : X ⟶ Y} {f' g' h' t' k' : X ⟶ Z}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g k)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f h) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso h t) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t k)
    (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (r' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' k')
    (q' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' h') (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso h' t') (a' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t' k')
    (hf : f ≫ i = f') (hg : g ≫ i = g') (hh : h ≫ i = h')
    (ht : t ≫ i = t') (hk : k ≫ i = k')
    (hc : HEq (c.postcomp i) c') (hr : HEq (r.postcomp i) r')
    (hq : HEq (q.postcomp i) q') (hd : HEq (d.postcomp i) d')
    (ha : HEq (a.postcomp i) a') (he : c' ≪≫ r' = q' ≪≫ d' ≪≫ a') :
    c ≪≫ r = q ≪≫ d ≪≫ a := by
  have heh : c'.hom ≫ r'.hom = q'.hom ≫ d'.hom ≫ a'.hom :=
    congrArg Iso.hom he
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_eq_of_heq (c.postcomp i).hom (r.postcomp i).hom
    (q.postcomp i).hom (d.postcomp i).hom (a.postcomp i).hom
    c'.hom r'.hom q'.hom d'.hom a'.hom hf hg hh ht hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hf hg hc) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hg hk hr)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hf hh hq) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hh ht hd)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ ht hk ha) heh
  apply Iso.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful hi
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, CategoryTheory.Functor.map_comp, Iso.trans_hom] using! hh
/-- 完全充満な実包含後の同じ指定三角経路の等式を、元の全関手同型へ反映する。 -/
lemma functorIso_two_one_reflect_postcomp {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (i : Y ⟶ Z) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    {f g k : X ⟶ Y} {f' g' k' : X ⟶ Z}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g k) (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f k)
    (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (r' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' k') (q' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' k')
    (hf : f ≫ i = f') (hg : g ≫ i = g') (hk : k ≫ i = k')
    (hc : HEq (c.postcomp i) c') (hr : HEq (r.postcomp i) r')
    (hq : HEq (q.postcomp i) q') (he : c' ≪≫ r' = q') : c ≪≫ r = q := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq (c.postcomp i).hom (r.postcomp i).hom c'.hom r'.hom
    hf hg hk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hf hg hc) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq _ _ hg hk hr)
  have hQ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (q.postcomp i) q' hf hk hq
  have heh : c'.hom ≫ r'.hom = q'.hom := congrArg Iso.hom he
  have hh := eq_of_heq (hL.trans ((heq_of_eq heh).trans hQ.symm))
  apply Iso.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful hi
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, CategoryTheory.Functor.map_comp,
    Iso.trans_hom] using! hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
