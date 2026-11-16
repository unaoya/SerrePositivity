module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedScalarModels
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent

/-!
# 制限した標準有限完備化単位の反転

## 概要
S の元の完備化単位を制限しても、元の R 完備化によって擬同型になる。

## 方針
既存の導来係数制限・完備化の自然同型と標準単位の冪等性だけを使う。

## 規約
複体上の同型の自然性を仮定せず、導来関手の比較を通じて実際の複体の射を判定する。

## 使われ方
BS 著者版 Lemma 4.22 の完備行模型の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の S 標準単位を制限した射は、同じ R 完備化で反転される。 -/
theorem restricted_finiteCompletionUnit_completion_quasiIso (f : R →+* S)
    {r : ℕ} (x : Fin r → R) (K : Complex S) :
    QuasiIso ((finiteCompletionFunctor x).map
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (finiteCompletionUnit (fun j => f (x j)) K))) := by
  let u := finiteCompletionUnit (fun j => f (x j)) K
  haveI : IsIso ((finiteDerivedCompletionFunctor (fun j => f (x j))).map
      (DerivedCategory.Q.map u)) := finiteDerivedCompletion_map_unit_isIso _ K
  have hR : IsIso ((finiteDerivedCompletionFunctor x).map
      ((derivedRestrictScalars f).map (DerivedCategory.Q.map u))) := by
    apply (NatIso.isIso_map_iff (finiteDerivedCompletionRestrictionIso f x)
      (DerivedCategory.Q.map u)).mpr
    change IsIso ((derivedRestrictScalars f).map
      ((finiteDerivedCompletionFunctor (fun j => f (x j))).map (DerivedCategory.Q.map u)))
    infer_instance
  have hQ : IsIso ((finiteDerivedCompletionFunctor x).map (DerivedCategory.Q.map
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map u))) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (derivedRestrictScalarsFactors f) (finiteDerivedCompletionFunctor x)) u).mp hR
  have hC : IsIso (DerivedCategory.Q.map ((finiteCompletionFunctor x).map
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map u))) :=
    (NatIso.isIso_map_iff (finiteDerivedCompletionComparison x)
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map u)).mp hQ
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp hC

/-- 完備化した S 複体の制限は、元の有限列の全座標について完備である。 -/
theorem restricted_finiteCompletion_isComplete (f : R →+* S) {r : ℕ}
    (x : Fin r → R) (K : Complex S) (j : Fin r) :
    IsComplete R (x j) (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        ((finiteCompletionFunctor (fun j => f (x j))).obj K))) :=
  isComplete_of_iso R (x j)
    ((derivedRestrictScalarsFactors f).app ((finiteCompletionFunctor (fun j => f (x j))).obj K))
    (derivedRestrictScalars_isComplete f (x j) _
      (finiteCompletion_isComplete (fun j => f (x j)) K j))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
