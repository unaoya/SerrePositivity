module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneKan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModulePiMooreNaturality

/-!
# 各段の π と指定 smart 切断のホモロジー

DAG XIII §2.2 のスペクトル忘却の π/H 比較への前段。
実 Γ の正規化の自然同型をホモロジーへ送り、既存の π/Moore 比較を合成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- 同じ段を単体的加群の台として記した場合の Kan 性。 -/
instance levelModuleUnderlyingKan (M : Complex A) (r : ℕ) :
    SSet.KanComplex (moduleUnderlyingSSet ((levelModuleFunctor A r).obj M)) := by
  change SSet.KanComplex ((levelSpaceFunctor A r).obj M)
  infer_instance

/-- 同じ Γ の余単位は、各鎖ホモロジー次数で自然同型を与える。 -/
def normalizedLevelHomologyIso (r d : ℕ) :
    levelModuleFunctor A r ⋙ (Abelian.DoldKan.N :
      SimplicialObject (ModuleCat A) ⥤ ChainComplex (ModuleCat A) ℕ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat A) (.down ℕ) d ≅
    levelChainFunctor A r ⋙
      HomologicalComplex.homologyFunctor (ModuleCat A) (.down ℕ) d :=
  Functor.isoWhiskerRight (normalizedLevelIso A r)
    (HomologicalComplex.homologyFunctor (ModuleCat A) (.down ℕ) d)

/-- 零基点での正次数 π は、指定 smart 切断の同じホモロジーである。 -/
def levelPiHomologyEquiv (M : Complex A) (r n : ℕ) :
    KanHomotopyGroup ((levelSpaceFunctor A r).obj M) n
      (0 : ((levelModuleFunctor A r).obj M).obj
        (Opposite.op (SimplexCategory.mk 0))) ≃*
      Multiplicative (((levelChainFunctor A r).obj M).homology (n + 1)) := by
  let W := (levelModuleFunctor A r).obj M
  letI : SSet.KanComplex (moduleUnderlyingSSet W) := by
    change SSet.KanComplex ((levelSpaceFunctor A r).obj M)
    infer_instance
  exact (modulePiMooreGroupEquiv W n).trans
    (additiveGroupToMultiplicativeEquiv
      ((normalizedLevelHomologyIso A r (n + 1)).app M).toLinearEquiv.toAddEquiv)

end SerrePositivity.EInfinity.PowerOperation
