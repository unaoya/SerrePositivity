module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation

/-!
概要：図式の厳密な表示変更を経ても、全族の制限の等式は保たれる。
方針：図式の等式による移送を帰納し、元の同じ制限へ戻す。
規約：全パラメータの射の等式を要求する。使われ方：右長辺上の底円柱の終端固定。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 図式の表示変更は、二つの全族の同じ部分への制限の一致を保つ。 -/
lemma cosliceDiagramChange_restriction_eq {K J B T : SSet.{u}} {p p' : K ⟶ B}
    (h : p = p') (j : J ⟶ K) (a b : T ⟶ sliceUnder p)
    (hab : a ≫ sliceUnderRestrict p j = b ≫ sliceUnderRestrict p j) :
    (a ≫ eqToHom (congrArg sliceUnder h)) ≫ sliceUnderRestrict p' j =
      (b ≫ eqToHom (congrArg sliceUnder h)) ≫ sliceUnderRestrict p' j := by
  cases h
  simpa only [eqToHom_refl, Category.comp_id] using hab

end SerrePositivity.InfinityCategories.HomotopyLimits
