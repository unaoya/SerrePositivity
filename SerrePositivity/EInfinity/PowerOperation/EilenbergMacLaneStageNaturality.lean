module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStageHomology

/-!
# 各段の π/H 比較の自然性

DAG XIII §2.2 の同じ指定段と全鎖写像を保つ。
π/Moore の自然性と、同じ Γ の余単位のホモロジーの自然性を合成する。
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
variable {A : Type u} [CommRing A] {M N : Complex A}

/-- 各段の同じ π/H 比較は任意の鎖写像で可換する。 -/
lemma levelPiHomologyEquiv_naturality (f : M ⟶ N) (r n : ℕ)
    (a : KanHomotopyGroup ((levelSpaceFunctor A r).obj M) n
      (0 : ((levelModuleFunctor A r).obj M).obj
        (Opposite.op (SimplexCategory.mk 0)))) :
    levelPiHomologyEquiv A N r n
      (KanHomotopyGroup.map
        (moduleUnderlyingSSetMap ((levelModuleFunctor A r).map f))
        (moduleUnderlyingSSetMap_zero ((levelModuleFunctor A r).map f)) a) =
    (HomologicalComplex.homologyMap ((levelChainFunctor A r).map f) (n + 1)).hom
      (levelPiHomologyEquiv A M r n a) := by
  change ((normalizedLevelHomologyIso A r (n + 1)).app N).hom.hom
    (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.modulePiMooreGroupEquiv ((levelModuleFunctor A r).obj N) n
      (KanHomotopyGroup.map
        (moduleUnderlyingSSetMap ((levelModuleFunctor A r).map f))
        (moduleUnderlyingSSetMap_zero ((levelModuleFunctor A r).map f)) a)) = _
  rw [modulePiMooreGroupEquiv_naturality]
  exact congrArg (fun g => g.hom
    (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.modulePiMooreGroupEquiv ((levelModuleFunctor A r).obj M) n a))
    ((normalizedLevelHomologyIso A r (n + 1)).hom.naturality f)

end SerrePositivity.EInfinity.PowerOperation
