module
public import SerrePositivity.KST.NonConnective.DGKappaConeChoiceComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery

/-!
概要：実 cone の選択比較を、同じ perfect 安定閉包の包含四角形へ接続する。
方針：指定 P の実比較を元の Perf 始域を介して合成し、同じ実導来包含から比較を反映する。
規約：現行の P 同値供給に条件付き。B′ の変更や全 dg 入力作用は実装しない。
使われ方：K-7 d4・e の模型選択比較を実商の核包含へ接続するための四角形。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I J : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I) (Q : DGKappaPerfectInput R D J)

/-- 同じ元の Perf を介した、二つの perfect 安定閉包の指定同値。 -/
def dgKappaConePerfectChoiceEquivalence :=
  P.isEquivalence.choose.symm.trans Q.isEquivalence.choose

/-- 指定同値と元の二つの実導来包含は、同じ P の包含比較で整合する。 -/
def dgKappaConePerfectChoiceDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaConePerfectChoiceEquivalence R D I J P Q).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D J) (dgKappaConePerfectObjects R D J) ≫
          dgKappaConeDerivedComparison R D J)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
        dgKappaConeDerivedComparison R D I) := by
  let p := P.isEquivalence.choose
  let FI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
    dgKappaConeDerivedComparison R D I
  have eQ := Q.inclusion.precomp p.inv
  have eP := P.inclusion.precomp p.inv
  have eI := p.invHomIso.postcomp FI
  have e := eQ ≪≫ eP.symm ≪≫ eI
  simpa only [dgKappaConePerfectChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose, Category.assoc, Category.id_comp, p, FI]
    using! e

/-- 元の perfect 包含と cone 比較の四角形は、実 cone 内の全関手同型で可換する。 -/
def dgKappaConePerfectChoiceInclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
        (dgKappaConeChoiceEquivalence R D I J).hom)
      ((dgKappaConePerfectChoiceEquivalence R D I J P Q).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D J) (dgKappaConePerfectObjects R D J)) := by
  apply (dgKappaConeDerivedComparison_isFullyFaithful R D J).preimageFunctorIso
  have eL := (dgKappaConeChoiceEquivalence_inclusionIso R D I J).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
  have eR := dgKappaConePerfectChoiceDerivedIso R D I J P Q
  simpa only [Category.assoc] using! eL ≪≫ eR.symm

end SerrePositivity.KST.NonConnective
