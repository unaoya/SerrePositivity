module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InverseComparisonCounit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoSelfUnitExchange

/-!
概要：同じ指定単位から構成した余単位の第二三角恒等式を証明する。
方針：第一三角恒等式を後合成し、指定単位の自己交換と前合成の忠実性を使う。
規約：元の逆射・単位・余単位を保持。使われ方：右 Hom 成分での指定比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ構成の余単位は、元の逆射上でも同じ指定単位の三角恒等式を満たす。 -/
lemma inverseComparisonCounit_triangle_inverse {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (r : Y ⟶ X) (u : FunctorIso (e.hom ≫ r) (𝟙 X)) :
    u.precomp r = (inverseComparisonCounit e r u).postcomp r := by
  have h := congrArg (fun k => FunctorIso.postcomp k r)
    (inverseComparisonCounit_triangle e r u)
  rw [functorIso_postcomp_postcomp, functorIso_precomp_postcomp,
    functorIso_unit_self_whisker] at h
  apply functorIso_precomp_injective_of_qCatEquivalence e.hom e.isQCatEquivalence
  change (u.precomp r).precomp e.hom =
    ((inverseComparisonCounit e r u).postcomp r).precomp e.hom
  rw [functorIso_precomp_precomp]
  exact h

end SerrePositivity.InfinityCategories.F2
