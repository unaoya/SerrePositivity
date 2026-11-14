module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneDerivedSourceComparison
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneNativeDiagram
public import SerrePositivity.EInfinity.PowerOperation.SemifreeClosedHoHomology

/-!
# 半自由閉零圏上での実 V_A の整数 π/H の全自然比較

DAG XIII §2.2 の native π/H 比較。指定された全 sourceIso をホモトピー圏へ送り、
同じ通常射の辺を通す。存在だけの対象ごとの比較へ置き換えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.KST.LocalizingInvariants
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A]

/-- 界面のホモロジーを乗法記法の可換群として読む。 -/
def derivedMultiplicativeCohomologyOnHo (j : ℤ) :=
  additiveCohomologyOnHo A (-j) ⋙ AddCommGrpCat.toCommGrp

def semifreeClosedHoMultiplicativeHomologyIso (j : ℤ) :
    dgClosedHoFunctor A (Semifree A) ⋙ derivedMultiplicativeCohomologyOnHo A j ≅
      semifreeClosedToComplex A ⋙ complexMultiplicativeCohomology A j :=
  Functor.isoWhiskerRight (semifreeClosedHoHomologyIso A (-j))
    (forget₂ (ModuleCat A) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp)

def eilenbergMacLaneSemifreePiComparison (j : ℤ) :
    dgClosedHoFunctor A (Semifree A) ⋙
      ((hoFunctor.map (eilenbergMacLaneDerived A)).toFunctor ⋙ SpectrumHo.piFunctor j) ≅
      semifreeClosedToComplex A ⋙ complexMultiplicativeCohomology A j := by
  let C := ClosedCategory A (Semifree A)
  let F := semifreeClosedToComplex A
  let N := (hoFunctor.map (eilenbergMacLaneOrdinaryNative A)).toFunctor
  have h₁ : dgClosedHoFunctor A (Semifree A) ⋙
      (hoFunctor.map (eilenbergMacLaneDerived A)).toFunctor ≅
      (ordinaryNerveHomotopyFunctor C ⋙ (hoFunctor.map (nerveMap F)).toFunctor) ⋙ N := by
    simpa only [C, F, N, dgClosedHoFunctor, Functor.map_comp,
      Cat.Hom.comp_toFunctor, Functor.assoc] using
      Functor.isoWhiskerLeft (ordinaryNerveHomotopyFunctor C)
        (eilenbergMacLaneDerived_semifreeSourceIso A).toNatIso
  have h₂ := Functor.isoWhiskerRight (ordinaryNerveHoNaturality F) N
  have h₃ := Functor.associator F (ordinaryNerveHomotopyFunctor (Complex A)) N ≪≫
    Functor.isoWhiskerLeft F (eilenbergMacLaneNativeHoDiagramIso A)
  exact Functor.isoWhiskerRight (h₁ ≪≫ h₂ ≪≫ h₃) (SpectrumHo.piFunctor j) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (eilenbergMacLaneNativeHomologyIso A j)

end SerrePositivity.EInfinity.PowerOperation
