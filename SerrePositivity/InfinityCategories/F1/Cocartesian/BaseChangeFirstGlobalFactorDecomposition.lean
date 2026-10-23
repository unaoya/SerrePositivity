module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeFirstGlobalPasting

/-!
概要：同じ第一辺を、元の制限自然性の逆と大域自然性の制限の指定合成へ分解する。
方針：第一辺の制限正方形の始点だけを正規化し、指定された第一因子を消去する。
規約：元の第一辺・全 Hom 作用・自然性の指定値を保持する。
使われ方：元の大域輸送の三角等式から局所自然性の三角等式を回収する。
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

/-- 同じ制限自然性の始点は、大域自然性を制限した同じ作用に正規化される。 -/
lemma cocartesianBaseChangeFirstGlobalRestriction_source :
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
      (cocartesianBaseChangeHomTransport k p q ≫
        cocartesianBaseChangeHomRestrictionZero l k p q) =
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
      cocartesianBaseChangeHomTransport k p q) ≫
        cocartesianBaseChangeHomRestrictionZero l k p q := by
  simp only [Category.assoc]

/-- 同じ始点の表示だけを正規化した、元の指定制限自然性。 -/
def cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso :=
  F2.functorIsoOfEq (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q) rfl

/-- 第一辺の指定因子は、制限自然性の逆と大域自然性の制限を貼った値。 -/
def CocartesianBaseChangeFirstGlobalFactorDecomposition : Prop :=
  FunctorIsoPastingRightFactorIdentity
    (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q) rfl rfl

/-- 同じ指定第一辺の、元の大域自然性への分解を回収する。 -/
lemma cocartesianBaseChangeFirstGlobalFactorDecomposition :
    CocartesianBaseChangeFirstGlobalFactorDecomposition l k p q := by
  have h := FunctorIsoPastingHEq.rightFactor
    (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q) rfl rfl
    (cocartesianBaseChangeFirstGlobalPasting l k p q)
  exact h

/-- 始点のみをそろえた元の第一辺の制限正方形は、同じ大域自然性に貼り合う。 -/
lemma cocartesianBaseChangeFirstGlobalPasting_normalized :
    FunctorIsoPastingSourceIdentity
      (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
      (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
      ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q))
      (cocartesianBaseChangeFirstGlobalRestriction_source l k p q) := by
  exact FunctorIsoPastingHEq.normalizeSource _ _ _ _
    (cocartesianBaseChangeFirstGlobalPasting l k p q)

end SerrePositivity.InfinityCategories
