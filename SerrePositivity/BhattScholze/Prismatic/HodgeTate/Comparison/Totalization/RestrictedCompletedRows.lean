module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedFiniteCompletionUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolvedScalarTotalCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardCompletedModelComparison

/-!
# 標準 S 完備行と固定 R 模型の比較

## 概要
実際の係数増大と S 完備化単位の合成を、R 完備化の後で比較する。

## 方針
制限した S 単位の反転と、完備な標的の元の R 単位を使う。

## 規約
自然性のない対象ごとの複体同型で水平図式を移さない。

## 使われ方
BS 著者版 Lemma 4.22 の同じ S 線形標準比較の同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の S 完備行を、そのまま R 上の複体へ制限する。 -/
abbrev restrictedCompletedBaseChangeRows (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) : CochainComplex (Complex R) ℕ :=
  restrictedRows f (standardCompletedBaseChangeRows f x K)

/-- 制限した元の各 S 完備行は、各 R 座標について完備である。 -/
theorem restrictedCompletedBaseChangeRows_isComplete (f : R →+* S) {r : ℕ}
    (x : Fin r → R) (K : CochainComplex (Complex R) ℕ) (n : ℕ) (j : Fin r) :
    IsComplete R (x j) (DerivedCategory.Q.obj ((restrictedCompletedBaseChangeRows f x K).X n)) :=
  restricted_finiteCompletion_isComplete f x (baseChange f (K.X n)) j

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 係数増大と元の S 合成単位からなる実際の水平図式の射。 -/
def toRestrictedCompletedRows {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) :
    tensorRows L.complex K ⟶ restrictedCompletedBaseChangeRows f x K :=
  L.comparisonRows K ≫
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)).map
      (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))

/-- 同じ水平図式の射を R 完備化する。 -/
def completedToRestrictedRows {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) :
    finiteCompletedRows x (tensorRows L.complex K) ⟶
      finiteCompletedRows x (restrictedCompletedBaseChangeRows f x K) :=
  ((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map (L.toRestrictedCompletedRows x K)

/-- K-flat な各行では、指定した R 完備化後の実際の射は擬同型である。 -/
theorem completedToRestrictedRows_quasiIso {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (n : ℕ) (hK : complexKFlat R (K.X n)) :
    QuasiIso ((L.completedToRestrictedRows x K).f n) := by
  change QuasiIso ((finiteCompletionFunctor x).map
    (L.comparison (K.X n) ≫
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (finiteCompletionUnit (fun j => f (x j)) (baseChange f (K.X n))))))
  rw [Functor.map_comp]
  haveI := L.comparison_quasiIso (K.X n) hK
  haveI := finiteCompletionFunctor_map_quasiIso x (L.comparison (K.X n))
  haveI := restricted_finiteCompletionUnit_completion_quasiIso f x (baseChange f (K.X n))
  infer_instance

/-- 制限した元の S 完備行の R 標準単位も擬同型である。 -/
theorem restrictedRowsUnit_quasiIso {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (n : ℕ) :
    QuasiIso ((finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K)).f n) := by
  have h := finiteCompletionUnit_isIso_of_isComplete x
    ((restrictedCompletedBaseChangeRows f x K).X n)
    (restrictedCompletedBaseChangeRows_isComplete f x K n)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp h

/-- 行ごとの計算同型。自然性を仮定せず、実際の二本の擬同型を使う。 -/
def restrictedCompletedRowIso {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (n : ℕ) (hK : complexKFlat R (K.X n)) :
    DerivedCategory.Q.obj ((finiteCompletedRows x (tensorRows L.complex K)).X n) ≅
      DerivedCategory.Q.obj ((restrictedCompletedBaseChangeRows f x K).X n) := by
  haveI := L.completedToRestrictedRows_quasiIso x K n hK
  haveI := restrictedRowsUnit_quasiIso (f := f) x K n
  exact asIso (DerivedCategory.Q.map ((L.completedToRestrictedRows x K).f n)) ≪≫
    (asIso (DerivedCategory.Q.map
      ((finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K)).f n))).symm

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
