module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeFirstGlobalNaturalityFactor
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeRestrictionRebasedNaturality

/-!
概要：元の第一辺と制限自然性の指定合成は、元の大域自然性の制限そのものである。
方針：元の分類作用へ端点を移した制限正方形を、同じ名前付き指定因子で表示する。
規約：元の全 Hom 作用と三辺の指定値を保持する。
使われ方：元の輸送三角形から局所自然性の三角等式を回収する。
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

/-- 元の底変換後の分類 Hom 作用に沿う、指定された制限自然性。 -/
def cocartesianBaseChangeFirstGlobalRestrictionIso :=
  (cocartesianBaseChangeHomTransport_restrictionIso l k p q).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))

/-- 指定された第一辺と制限自然性の合成は、同じ大域自然性の制限を回収する。 -/
def CocartesianBaseChangeFirstGlobalPasting : Prop :=
  FunctorIsoPastingHEq (cocartesianBaseChangeFirstGlobalRestrictionIso l k p q)
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))

/-- 元の名前付き指定因子で表示した、第一辺の制限正方形の貼り合わせ等式。 -/
lemma cocartesianBaseChangeFirstGlobalPasting :
    CocartesianBaseChangeFirstGlobalPasting l k p q := by
  exact cocartesianBaseChangeHomTransport_restrictionIso_rebasedNaturality_heq l k p q

end SerrePositivity.InfinityCategories
