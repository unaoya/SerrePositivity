module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStageHomology
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModulePiZeroMoore

/-!
# Γ の各段の連結成分と H⁰ の比較

DAG XIII §2.2 のスペクトル忘却への前段。Ω 条件で必要な零次数も含め、
正規化の同じ余単位から比較を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

/-- 各段の成分は、同じ smart 切断の零次ホモロジーである。 -/
def levelPiZeroHomologyEquiv (M : Complex A) (r : ℕ) :
    SSet.π₀ ((levelSpaceFunctor A r).obj M) ≃
      (((levelChainFunctor A r).obj M).homology 0) :=
  (modulePiZeroMooreEquiv ((levelModuleFunctor A r).obj M)).trans
    ((normalizedLevelHomologyIso A r 0).app M).toLinearEquiv.toEquiv

/-- 同じ成分比較の終域を元の H^r へ戻す。 -/
def levelPiZeroCohomologyEquiv (M : Complex A) (r : ℕ) :
    SSet.π₀ ((levelSpaceFunctor A r).obj M) ≃ M.homology (r : ℤ) :=
  (levelPiZeroHomologyEquiv A M r).trans
    ((levelCohomologyIso A M r 0) ≪≫
      (show M.homology ((r : ℤ) - (0 : ℕ)) ≅ M.homology (r : ℤ) from
        eqToIso (congrArg (fun i : ℤ => M.homology i) (by simp)))).toLinearEquiv.toEquiv

lemma levelPiZeroHomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (r : ℕ) (a : SSet.π₀ ((levelSpaceFunctor A r).obj M)) :
    levelPiZeroHomologyEquiv A N r
      (SSet.mapπ₀ (moduleUnderlyingSSetMap ((levelModuleFunctor A r).map f)) a) =
    (HomologicalComplex.homologyMap ((levelChainFunctor A r).map f) 0).hom
      (levelPiZeroHomologyEquiv A M r a) := by
  change ((normalizedLevelHomologyIso A r 0).app N).hom.hom
    (modulePiZeroMooreEquiv ((levelModuleFunctor A r).obj N)
      (SSet.mapπ₀ (moduleUnderlyingSSetMap ((levelModuleFunctor A r).map f)) a)) = _
  rw [modulePiZeroMooreEquiv_naturality]
  exact congrArg (fun g => g.hom
    (modulePiZeroMooreEquiv ((levelModuleFunctor A r).obj M) a))
    ((normalizedLevelHomologyIso A r 0).hom.naturality f)

end SerrePositivity.EInfinity.PowerOperation
