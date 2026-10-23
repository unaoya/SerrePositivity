module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalNativeGlobalEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalRestrictionGlobalCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalNativeRestrictionCoherence

/-!
概要：既存の局所自然性の第一因子を元の全 Hom に戻して、同じ両端・指定値を回収する。
方針：同じ二段の底変換を二重底変換へまとめ、既存の局所結合比較の回収を使う。
規約：元の全 Hom と同じ底変換・指定局所自然性を保持する。
使われ方：既存の局所自然性全体と元の大域三角形の指定合成の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二段の前合成は、既存の局所結合比較と同じ両端を回収する。 -/
lemma cocartesianLocalNativeRestrictionNativeFactor_originalHom_endpoints :
    ((cocartesianLocalNativeRestrictionNativeFactorIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).sourceMap =
      (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap ∧
    ((cocartesianLocalNativeRestrictionNativeFactorIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).targetMap =
      (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap := by
  have h₀ := FunctorIso.precomp_precomp_endpoints
    (cocartesianIteratedLocalHomComparison_nativeIso l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q) rfl
  have h₁ := cocartesianIteratedLocalHomComparison_nativeIso_originalHom_endpoints l k p q
  exact ⟨h₀.1.trans h₁.1, h₀.2.trans h₁.2⟩

/-- 元の二段の前合成は、既存の局所結合比較と同じ指定値を回収する。 -/
lemma cocartesianLocalNativeRestrictionNativeFactor_originalHom_heq :
    HEq (cocartesianBaseChangeGlobalNativeComparisonIso l k p q)
      ((cocartesianLocalNativeRestrictionNativeFactorIso l k p q).precomp
        (cocartesianSingleBaseChangeHomAction k p q)) := by
  exact functorIso_precomp_precomp_of_value_heq
    (cocartesianIteratedLocalHomComparison_nativeIso l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q) rfl
    (cocartesianBaseChangeGlobalNativeComparisonIso l k p q)
    (cocartesianIteratedLocalHomComparison_nativeIso_originalHom_heq l k p q)

end SerrePositivity.InfinityCategories
