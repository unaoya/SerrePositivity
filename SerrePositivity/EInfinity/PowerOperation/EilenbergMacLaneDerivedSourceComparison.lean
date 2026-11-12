module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneDerivedFunctor
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeNerveUp
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeClosedDerivedComparison

/-!
# 実 V_A の元の全複体・半自由閉零圏上の全始域比較

DAG XIII §2.2 のスペクトル忘却の π/H 比較への前段。
指定局所化と同じ全二胞体を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- V_A は元の全複体の通常図式へ、同じ全関手の同型で戻る。 -/
def eilenbergMacLaneDerived_ordinarySourceIso :
    FunctorIso (complexOrdinaryDerivedSource A ≫ eilenbergMacLaneDerived A)
      (eilenbergMacLaneOrdinaryNative A) := by
  simpa only [complexRelativeDerivedSource, complexRelativeSpectrumSource, ← Category.assoc,
    complexRelativeNerveUp_down, Category.id_comp] using
      (eilenbergMacLaneDerived_sourceIso A).precomp (complexRelativeNerveUp A)

/-- 半自由閉零圏での同じ全比較。native D(A) の全射の π/H 自然性に使う。 -/
def eilenbergMacLaneDerived_semifreeSourceIso :
    FunctorIso (closedNerveInclusion A (Semifree A) ≫ eilenbergMacLaneDerived A)
      (nerveMap (semifreeClosedToComplex A) ≫ eilenbergMacLaneOrdinaryNative A) := by
  have h₁ := FunctorIso.postcomp (semifreeClosedDerivedSourceIso A).symm
    (eilenbergMacLaneDerived A)
  have h₂ := (eilenbergMacLaneDerived_ordinarySourceIso A).precomp
    (nerveMap (semifreeClosedToComplex A))
  have h₁' : FunctorIso (closedNerveInclusion A (Semifree A) ≫ eilenbergMacLaneDerived A)
      (nerveMap (semifreeClosedToComplex A) ≫
        (complexOrdinaryDerivedSource A ≫ eilenbergMacLaneDerived A)) := by
    simpa only [Category.assoc] using h₁
  exact h₁'.trans h₂

end SerrePositivity.EInfinity.PowerOperation
