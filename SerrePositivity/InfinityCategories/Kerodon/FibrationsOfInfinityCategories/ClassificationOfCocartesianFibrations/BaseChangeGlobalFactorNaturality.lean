module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeNaturalityFactorCoherence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeFirstRestrictionFactor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

/-!
概要：元の制限正方形の源の指定因子比較を、元の大域自然性と同じ端点へ移す。
方針：元の span の両射影が回収する作用を使い、同じ指定値を正規化する。
規約：元の全 Hom 作用と指定切断・指定自然性を保持する。
使われ方：第一辺の制限正方形を局所自然性の三角等式へ移す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上の指定 span の因子比較。 -/
def cocartesianBaseChangeGlobalFactorIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanOne k p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanZero k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanOneSection k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomComparison k p q)

/-- 元の因子比較の始点は同じ底変換の分類作用と指定輸送の合成。 -/
lemma cocartesianBaseChangeGlobalFactor_source :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomComparison k p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomSpanOne k p q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport k p q) =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport k p q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomComparison_one]
  exact Category.assoc _ _ _

/-- 同じ因子比較を正規化すると、元の大域自然性そのものを回収する。 -/
lemma cocartesianBaseChangeGlobalFactorIso_normalized :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (cocartesianBaseChangeGlobalFactorIso k p q)
      (cocartesianBaseChangeGlobalFactor_source k p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomComparison_zero k p q) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q := by
  exact eq_of_heq (HEq.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso_factor_heq k p q).symm)

/-- 元の制限後も、正規化した源の因子比較は同じ大域自然性の指定値を保持する。 -/
lemma cocartesianBaseChangeGlobalFactorIso_restriction_heq
    {A : Type u} [Category.{u} A] (l : A ⥤ D) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q))
      ((cocartesianBaseChangeGlobalFactorIso k p q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq_of_eq
    (cocartesianBaseChangeGlobalFactorIso k p q)
    (cocartesianBaseChangeGlobalFactor_source k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomComparison_zero k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q)
    (cocartesianBaseChangeGlobalFactorIso_normalized k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
