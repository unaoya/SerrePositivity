module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalRestrictionGlobalCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoEndpointPrecomposition

/-!
概要：既存の局所制限自然性を元の全 Hom に戻した両端は、同じ指定第二因子の両端。
方針：元の二因子の端点回収を、同じ端点正規化と前合成の一般則で運ぶ。
規約：元の全 Hom 作用と既存の指定制限自然性を保持する。
使われ方：既存の指定局所自然性を元の全 Hom 上で貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所制限自然性は、元の一回目の底変換で前合成しても同じ両端を回収する。 -/
lemma cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_endpoints
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    ((cocartesianIteratedLocalHomComparison_restrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).sourceMap =
      (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q).sourceMap ∧
    ((cocartesianIteratedLocalHomComparison_restrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).targetMap =
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap := by
  have hs₀ := functorIso_precomp_sourceMap_recover
    (cocartesianIteratedLocalRestrictionNaturalityIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianBaseChangeGlobalRestrictionNaturality_endpoints l k p q).1
  have hs := functorIsoOfEq_precomp_sourceMap_of_eq
    (cocartesianIteratedLocalRestrictionCompositeIso l k p q)
    (cocartesianIteratedLocalRestrictionComposite_source l k p q)
    (cocartesianIteratedLocalRestrictionComposite_target l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    hs₀
  have hi := functorIso_normalized_symm_precomp_precomp_target
    (cocartesianBaseChangeHomTransport_restrictionIso l k p q)
    (cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianIteratedLocalRestrictionInverse_source l k p q)
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q)
  have ht₀ := functorIsoOfEq_precomp_targetMap_recover
    (cocartesianIteratedLocalRestrictionInverseIso l k p q)
    (cocartesianIteratedLocalRestrictionInverse_source l k p q)
    (cocartesianSingleBaseChangeHomAction k p q) hi
  have ht := functorIsoOfEq_precomp_targetMap_of_eq
    (cocartesianIteratedLocalRestrictionCompositeIso l k p q)
    (cocartesianIteratedLocalRestrictionComposite_source l k p q)
    (cocartesianIteratedLocalRestrictionComposite_target l k p q)
    (cocartesianSingleBaseChangeHomAction k p q) ht₀
  exact ⟨hs, ht⟩

end SerrePositivity.InfinityCategories
