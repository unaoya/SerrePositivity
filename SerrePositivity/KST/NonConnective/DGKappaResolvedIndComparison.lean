module
public import SerrePositivity.KST.NonConnective.DGKInputIndMorita
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaNativePComparison

/-!
概要：D-8 の同じ実小核と元の固定 ν 値の評価 Morita／P 比較を、同じ Indω へ延長する。
方針：指定順射を保持する Yoneda 延長と、制限同値の充満忠実性を使う。
規約：I・P の実比較を消費する。非可算 κ-cone 自体を Indω と同一視しない。
使われ方：K-7 d4 の実小核・元の P・I-2 e の無条件 compact 生成界面の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R A κ) (P : DGKappaPerfectInput R A I)
local notation "B" => dgKappaResolvedKernelKInput R A I

/-- 元の実評価 Morita 順射を、同じ核側 Yoneda に続けた生成元上の関手。 -/
def dgKappaResolvedIndMoritaGenerator :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A I P).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj

/-- 同じ実評価 Morita 順射の指定 Indω 延長。 -/
def dgKappaResolvedIndMoritaMap : dgKInputIndCompletion R A ⟶ dgKInputIndCompletion R B :=
  dgKInputIndExtension R A B (dgKappaResolvedIndMoritaGenerator R A I P)

/-- 元の P／Yoneda の指定全合成も、同じ制限同値で延長する。 -/
def dgKappaResolvedIndPGenerator :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePExactMap R A I P).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj

def dgKappaResolvedIndPMap : dgKInputIndCompletion R A ⟶ dgKInputIndCompletion R B :=
  dgKInputIndExtension R A B (dgKappaResolvedIndPGenerator R A I P)

/-- 両実延長は同じ小 filtered 余極限を保存する。 -/
theorem dgKappaResolvedIndMoritaMap_preservesFilteredColimits :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 (dgKappaResolvedIndMoritaMap R A I P) :=
  dgKInputIndExtension_preservesFilteredColimits R A B _

theorem dgKappaResolvedIndPMap_preservesFilteredColimits :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 (dgKappaResolvedIndPMap R A I P) :=
  dgKInputIndExtension_preservesFilteredColimits R A B _

/-- 元の指定 Morita 順射を保つ、同じ二つの Indω の実同値。 -/
def dgKappaResolvedIndEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKInputIndCompletion R A) (dgKInputIndCompletion R B) :=
  dgKInputIndEquivalence R A B
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{max (u + 1) v, max (u + 1) v + 1}
      (dgKappaResolvedKernelPerfQCatEquivalence R A I P).isQCatEquivalence).choose

/-- 同値の順射は指定した実 Morita 延長そのものである。 -/
theorem dgKappaResolvedIndEquivalence_hom :
    (dgKappaResolvedIndEquivalence R A I P).hom = dgKappaResolvedIndMoritaMap R A I P := rfl

/-- 元の P と実評価 Morita 比較を、点別比較へ弱めず全 Indω 上へ延長する。 -/
def dgKappaResolvedIndPComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaResolvedIndPMap R A I P) (dgKappaResolvedIndMoritaMap R A I P) := by
  have eP := dgKInputIndExtension_restrictionIso R A B (dgKappaResolvedIndPGenerator R A I P)
  have eM := dgKInputIndExtension_restrictionIso R A B (dgKappaResolvedIndMoritaGenerator R A I P)
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{max (u + 1) v, max (u + 1) v + 1}
    (dgKappaResolvedYonedaFixedPerfComparison R A I P)).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj)
  exact dgKInputIndFunctorIso_of_restriction R A B _ _
    (dgKappaResolvedIndPMap_preservesFilteredColimits R A I P)
    (dgKappaResolvedIndMoritaMap_preservesFilteredColimits R A I P) (eP ≪≫ e ≪≫ eM.symm)

/-- 同じ評価同値の Yoneda 制限は、元の全生成元上の指定 Morita 射を回収する。 -/
def dgKappaResolvedIndEquivalence_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫
      (dgKappaResolvedIndEquivalence R A I P).hom)
      (dgKappaResolvedIndMoritaGenerator R A I P) :=
  dgKInputIndExtension_restrictionIso R A B _

end SerrePositivity.KST.NonConnective
