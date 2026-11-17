module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedCompletedRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionReduction

/-!
# 制限した S 完備行の Tot の同じ計算模型

## 概要
実際の水平図式の二本の射を使い、固定 R 模型と制限した S 完備行の Tot を比較する。

## 方針
有限完全 Tor 振幅からの同じ一様下界を保ち、行ごとの擬同型を指定した積 Tot へ渡す。

## 規約
比較は元の標準単位と可換である。

## 使われ方
BS 著者版 Lemma 4.22 の標準 S 線形比較の同型性。
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

/-- 元の導来圏の同型を、指定した複体のホモロジーへ渡す。 -/
def homologyIsoOfDerivedIso {K M : Complex R}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj M) (i : ℤ) :
    K.homology i ≅ M.homology i :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app M

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)
include L

/-- 制限した元の S 完備行にも、固定 R 模型の同じ一様下界がある。 -/
theorem restrictedCompletedRows_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n)) :
    ∀ n : ℕ, ∀ i : ℤ, i < b-(c : ℤ) →
      IsZero (((restrictedCompletedBaseChangeRows f x K).X n).homology i) := by
  intro n i hi
  have hz := ScalarResolution.finiteCompletedTensor_lowerBound L x c hf (K.X n) b (hK n) i hi
  exact hz.of_iso
    (homologyIsoOfDerivedIso (L.restrictedCompletedRowIso x K n (hFlat n)) i).symm

/-- 再完備化の前後は同じ行の擬同型なので、下界も変わらない。 -/
theorem completedRestrictedRows_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n)) :
    ∀ n : ℕ, ∀ i : ℤ, i < b-(c : ℤ) →
      IsZero (((finiteCompletedRows x (restrictedCompletedBaseChangeRows f x K)).X n).homology i) := by
  intro n i hi
  haveI := restrictedRowsUnit_quasiIso (f := f) x K n
  have hz := restrictedCompletedRows_lowerBound L x c hf K b hK hFlat n i hi
  exact hz.of_iso
    (isoOfQuasiIsoAt ((finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K)).f n) i).symm

/-- 実際の二本の水平射から、同じ指定積 Tot の計算同型を得る。 -/
def restrictedCompletedRowsTotalIso {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n)) :
    DerivedCategory.Q.obj (total (finiteCompletedRows x (tensorRows L.complex K))) ≅
      DerivedCategory.Q.obj (total (restrictedCompletedBaseChangeRows f x K)) := by
  have hA : ∀ n : ℕ, ∀ i : ℤ, i < b-(c : ℤ) →
      IsZero (((finiteCompletedRows x (tensorRows L.complex K)).X n).homology i) :=
    fun n i hi => L.finiteCompletedTensor_lowerBound x c hf (K.X n) b (hK n) i hi
  have hB := L.restrictedCompletedRows_lowerBound x c hf K b hK hFlat
  have hCB := L.completedRestrictedRows_lowerBound x c hf K b hK hFlat
  haveI := total_map_quasiIso_of_rows (L.completedToRestrictedRows x K) (b-(c : ℤ)) hA hCB
    (fun n => L.completedToRestrictedRows_quasiIso x K n (hFlat n))
  haveI := total_map_quasiIso_of_rows
    (finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K)) (b-(c : ℤ)) hB hCB
    (restrictedRowsUnit_quasiIso (f := f) x K)
  exact asIso (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (L.completedToRestrictedRows x K))) ≪≫
    (asIso (DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K))))).symm


end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
