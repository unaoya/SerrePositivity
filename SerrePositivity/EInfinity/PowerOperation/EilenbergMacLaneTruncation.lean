module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLevels
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# 指定 smart 切断のホモロジーと元の複体

DAG XIII §2.2 の π/H 比較への前段。
延長と同じ切断の包含の準同型性から、境界次数を含めて元のホモロジーへ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 指定された smart 切断の H_d は、元の H^{-d} に等しい。 -/
def smartTruncationHomologyIso (M : Complex A) (d : ℕ) :
    (M.truncLE' (ComplexShape.embeddingUpIntLE 0)).homology d ≅
      M.homology (-(d : ℤ)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  have hd : e.f d = -(d : ℤ) := by simp [e]
  letI : QuasiIsoAt (HomologicalComplex.ιTruncLE M e) (-(d : ℤ)) :=
    HomologicalComplex.quasiIsoAt_ιTruncLE M e hd
  exact ((M.truncLE' e).extendHomologyIso e hd).symm ≪≫
    (homologyFunctor (ModuleCat A) (.up ℤ) (-(d : ℤ))).mapIso (M.truncLEIso e).symm ≪≫
      asIso (homologyMap (HomologicalComplex.ιTruncLE M e) (-(d : ℤ)))

/-- 第 r 段の H_d は元の複体の H^{r-d} である。 -/
def levelCohomologyIso (M : Complex A) (r d : ℕ) :
    ((levelChainFunctor A r).obj M).homology d ≅
      M.homology ((r : ℤ) - (d : ℤ)) :=
  smartTruncationHomologyIso A ((shiftFunctor (Complex A) (r : ℤ)).obj M) d ≪≫
    (((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
      (r : ℤ) (-(d : ℤ)) ((r : ℤ) - (d : ℤ)) (by omega)).app M)

end SerrePositivity.EInfinity.PowerOperation
