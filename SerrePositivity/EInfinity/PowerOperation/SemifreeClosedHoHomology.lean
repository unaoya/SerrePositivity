module

public import SerrePositivity.EInfinity.PowerOperation.DGClosedHoFull
public import SerrePositivity.EInfinity.Interface.Theory

/-!
# 半自由閉零圏での native D(A) ホモロジーの全比較

DAG XIII §2.2 の π/H 自然同型のホモロジー側。同じ H⁰ 商・既存の導来比較・
Mathlib のホモロジー比較を接続する。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A]

lemma semifreeClosedHomotopyComparison_fac :
    toHomotopy A (Semifree A) ⋙ semifreeHomotopyComparison A =
      semifreeClosedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) := by
  change (toHomotopy A (Semifree A) ⋙
    (dgFullSubcategoryInclusion A (Complex A) (Semifree.complexSemifree A)).onHomotopy) ⋙
      complexHomotopyComparison A = _
  rw [DGFunctor.onHomotopy_fac, Functor.assoc, complexHomotopyComparison_fac]
  rfl

/-- 同じ閉零圏上で、界面の native ホモロジーは元の複体のホモロジーと自然同型。 -/
def semifreeClosedHoHomologyIso (i : ℤ) :
    dgClosedHoFunctor A (Semifree A) ⋙ cohomologyOnHo A i ≅
      semifreeClosedToComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i := by
  let Q := dgClosedHoFunctor A (Semifree A)
  let B := (homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)).inverse
  let H := _root_.HomotopyCategory.homologyFunctor (ModuleCat A) (.up ℤ) i
  have h₁ : Q ⋙ cohomologyOnHo A i ≅
      ((Q ⋙ B) ⋙ ((derivedInfinityH0Equivalence A).functor ⋙
        semifreeHomotopyComparison A)) ⋙ H := by
    exact Functor.isoWhiskerLeft (Q ⋙ B) (derivedInfinityHomologyComparison A i)
  have hQ : (Q ⋙ B) ⋙ (derivedInfinityH0Equivalence A).functor =
      toHomotopy A (Semifree A) := dgClosedHoFunctor_comp_H0 A (Semifree A)
  have h₂ : (Q ⋙ B) ⋙ ((derivedInfinityH0Equivalence A).functor ⋙
      semifreeHomotopyComparison A) ≅
      semifreeClosedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) := by
    apply eqToIso
    rw [← Functor.assoc, hQ, semifreeClosedHomotopyComparison_fac]
  exact h₁ ≪≫ Functor.isoWhiskerRight h₂ H ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (semifreeClosedToComplex A)
      (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat A) (.up ℤ) i)

end SerrePositivity.EInfinity.PowerOperation
