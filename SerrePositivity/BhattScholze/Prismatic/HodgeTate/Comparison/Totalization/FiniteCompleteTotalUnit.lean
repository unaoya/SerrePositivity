module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletedComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalQuasiIso

/-!
# 完備な行の元の単位と積Tot

## 概要
全行が同じ指定座標で導来完備なら、一様下界の下で元の行の完備化単位のTotも擬同型。

## 方針
元の各行の単位の擬同型性を使い、その像の同じ一様下界を供給する。

## 規約
行をsingleに限定せず、元の指定単位をそのまま使う。

## 使われ方
元の通常係数拡大した行から標準完備行への比較の同型性。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open HomologicalAlgebra DifferentialGraded DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の各行が完備で一様下界を持つなら、同じ元の行単位のTotは擬同型。 -/
theorem finiteCompletionRowsUnit_total_quasiIso_of_complete {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hc : ∀ n : ℕ, ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj (K.X n))) :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (finiteCompletionRowsUnit x K)) := by
  have hq (n : ℕ) : QuasiIso ((finiteCompletionRowsUnit x K).f n) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
      (finiteCompletionUnit_isIso_of_isComplete x (K.X n) (hc n))
  apply total_map_quasiIso_of_rows _ b hK
    (fun n i hi => (hK n i hi).of_iso (isoOfQuasiIsoAt ((finiteCompletionRowsUnit x K).f n) i).symm)
    hq

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
