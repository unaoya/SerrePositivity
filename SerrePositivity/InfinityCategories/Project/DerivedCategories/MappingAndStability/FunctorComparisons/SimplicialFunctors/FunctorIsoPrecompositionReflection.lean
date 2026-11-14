module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
/-!
概要：完全充満な全前合成から、同じ指定全関手同型の等式を反映する。
方針：全関手同型の実交換則と同じ指定値の等式を使う。
規約：新しい比較を選ばない。使われ方：元の導来 kernel 合成子の coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
/-- 完全充満な全前合成後に一致する指定同型は、元の全関手同型として一致する。 -/
lemma functorIso_precomp_eq_of_isFullyFaithful {X A Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L).app Y))
    {f g : A ⟶ Y} (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (h : a.precomp L = b.precomp L) : a = b := by
  apply Iso.ext
  apply hL.toHoFullyFaithful.map_injective
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso, CategoryTheory.Functor.mapIso_hom] using!
    congrArg Iso.hom h
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
