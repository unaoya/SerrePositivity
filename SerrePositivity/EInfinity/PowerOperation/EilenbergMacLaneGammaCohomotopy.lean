module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaComponents
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePointedLimits
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStageNaturality
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
# 元の Γ の正次数の自然な π/H 比較

DAG XIII §2.2 の零次数の Ω 比較への前段。シフトした段に限らず、
元の Γ の全複体射について同じ正規化余単位と切断包含を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

instance gammaModuleUnderlyingKan (M : Complex A) :
    SSet.KanComplex (moduleUnderlyingSSet (gammaModule A M)) := gammaUnderlyingKan A M

instance gammaModuleFunctorUnderlyingKan (M : Complex A) :
    SSet.KanComplex (moduleUnderlyingSSet ((gammaModuleFunctor A).obj M)) :=
  gammaUnderlyingKan A M

/-- 同じ実 Γ の正規化により、正次数の π を切断のホモロジーへ戻す。 -/
def gammaPiHomologyEquiv (M : Complex A) (n : ℕ) :
    KanHomotopyGroup (gammaPointed A M).right n (gammaPointed A M).basepoint ≃*
      Multiplicative ((M.truncLE' (ComplexShape.embeddingUpIntLE 0)).homology (n + 1)) := by
  have : SSet.KanComplex (moduleUnderlyingSSet (gammaModule A M)) := gammaUnderlyingKan A M
  exact (modulePiMooreGroupEquiv (gammaModule A M) n).trans
    (additiveGroupToMultiplicativeEquiv
      ((normalizedGammaHomologyIso A (n + 1)).app M).toLinearEquiv.toAddEquiv)

lemma gammaPiHomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N) (n : ℕ)
    (a : KanHomotopyGroup (gammaPointed A M).right n (gammaPointed A M).basepoint) :
    gammaPiHomologyEquiv A N n
      (KST.Spectra.pointedGroupMap n ((gammaPointedFunctor A).map f) a) =
      Multiplicative.ofAdd
        ((homologyMap (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) (n + 1)).hom
          (Multiplicative.toAdd (gammaPiHomologyEquiv A M n a))) := by
  let f' : gammaModule A M ⟶ gammaModule A N := (gammaModuleFunctor A).map f
  let a' : KanHomotopyGroup (moduleUnderlyingSSet (gammaModule A M)) n 0 := a
  have hπ := modulePiMooreGroupEquiv_naturality f' n a'
  have h₁ := congrArg (fun z => Multiplicative.ofAdd
    (((normalizedGammaHomologyIso A (n + 1)).app N).hom.hom
      (Multiplicative.toAdd z))) hπ
  have h₂ := congrArg (fun g => Multiplicative.ofAdd (g.hom
    (Multiplicative.toAdd (modulePiMooreGroupEquiv (gammaModule A M) n a'))))
    ((normalizedGammaHomologyIso A (n + 1)).hom.naturality f)
  exact h₁.trans h₂

/-- 同じ正次数の π を、元の複体の H^{-n-1} と比較する。 -/
def gammaPiCohomologyEquiv (M : Complex A) (n : ℕ) :
    KanHomotopyGroup (gammaPointed A M).right n (gammaPointed A M).basepoint ≃*
      Multiplicative (M.homology (-((n + 1 : ℕ) : ℤ))) :=
  (gammaPiHomologyEquiv A M n).trans
    (additiveGroupToMultiplicativeEquiv
      (smartTruncationHomologyIso A M (n + 1)).toLinearEquiv.toAddEquiv)

lemma gammaPiCohomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N) (n : ℕ)
    (a : KanHomotopyGroup (gammaPointed A M).right n (gammaPointed A M).basepoint) :
    gammaPiCohomologyEquiv A N n
      (KST.Spectra.pointedGroupMap n ((gammaPointedFunctor A).map f) a) =
      Multiplicative.ofAdd ((homologyMap f (-((n + 1 : ℕ) : ℤ))).hom
        (Multiplicative.toAdd (gammaPiCohomologyEquiv A M n a))) := by
  change Multiplicative.ofAdd ((smartTruncationHomologyIso A N (n + 1)).hom.hom
    (Multiplicative.toAdd (gammaPiHomologyEquiv A N n
      (KST.Spectra.pointedGroupMap n ((gammaPointedFunctor A).map f) a)))) = _
  rw [gammaPiHomologyEquiv_naturality]
  exact congrArg (fun k => Multiplicative.ofAdd (k.hom
    (Multiplicative.toAdd (gammaPiHomologyEquiv A M n a))))
    (smartTruncationHomologyIso_naturality f (n + 1))

end SerrePositivity.EInfinity.PowerOperation
