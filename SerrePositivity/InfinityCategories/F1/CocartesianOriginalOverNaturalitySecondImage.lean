module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalOverNaturalityTriangleEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoChainTransport

/-!
概要：正規化前の大域自然性の第二辺は、同じ指定第二辺を正規化後に回収する。
方針：元の底上の制限の正規化と後合成の合成則を適用する。
規約：元の指定自然性と元の制限を保持する。
使われ方：同じ over 自然性の三角等式を反映する。
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

/-- 同じ第二辺の像は、元の三角等式に現れる指定第二辺そのもの。 -/
lemma cocartesianOriginalOverNaturalitySecondIso_postcomp_heq :
    HEq ((cocartesianOriginalOverNaturalitySecondIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
      ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q)) := by
  exact (heq_of_eq (F2.functorIso_postcomp_postcomp
    (cocartesianBaseChangeHomNaturalityIso k p q)
    (cocartesianBaseChangeHomOverRestriction l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q))).trans
    (F2.functorIso_postcomp_heq_of_map_eq (cocartesianBaseChangeHomNaturalityIso k p q)
      (cocartesianLocalHomOverRestriction_normalization l k p q)).symm

/-- 同じ第二辺の像は、正規化後の指定第二辺の終点を回収する。 -/
lemma cocartesianOriginalOverNaturalitySecondIso_postcomp_target :
    (cocartesianOriginalOverNaturalitySecondIso l k p q).targetMap ≫
      cocartesianBaseChangeHomCompositionNormalization l k p q =
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q)).targetMap := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ (cocartesianBaseChangeHomNaturalityIso k p q).targetMap ≫ m)
      (cocartesianLocalHomOverRestriction_normalization l k p q))

end SerrePositivity.InfinityCategories
