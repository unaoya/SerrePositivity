module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStageHomology
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncation

/-!
# 正次数の各段の π を元の複体の H へ戻す

DAG XIII §2.2 のスペクトル忘却の整数 π/H 比較の各段での式。
まだスペクトル構造射や native な忘却関手の存在は主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- 第 r 段の π_{n+1} は、元の H^{r-(n+1)} と同じ群である。 -/
def levelPiCohomologyEquiv (M : Complex A) (r n : ℕ) :
    KanHomotopyGroup ((levelSpaceFunctor A r).obj M) n
      (0 : ((levelModuleFunctor A r).obj M).obj
        (Opposite.op (SimplexCategory.mk 0))) ≃*
      Multiplicative (M.homology ((r : ℤ) - ((n : ℤ) + 1))) :=
  (levelPiHomologyEquiv A M r n).trans
    (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
      (levelCohomologyIso A M r (n + 1)).toLinearEquiv.toAddEquiv)

/-- 安定次数 j に合う正次数の段では、同じ比較の終域は H^{-j} となる。 -/
def levelPiCohomologyEquivAt (M : Complex A) (j : ℤ) (r n : ℕ)
    (h : (n : ℤ) + 1 = j + (r : ℤ)) :
    KanHomotopyGroup ((levelSpaceFunctor A r).obj M) n
      (0 : ((levelModuleFunctor A r).obj M).obj
        (Opposite.op (SimplexCategory.mk 0))) ≃* Multiplicative (M.homology (-j)) :=
  (levelPiCohomologyEquiv A M r n).trans
    (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
      (show M.homology ((r : ℤ) - ((n : ℤ) + 1)) ≅ M.homology (-j) from
        eqToIso (congrArg (fun i : ℤ => M.homology i) (by omega :
          (r : ℤ) - ((n : ℤ) + 1) = -j))).toLinearEquiv.toAddEquiv)

end SerrePositivity.EInfinity.PowerOperation
