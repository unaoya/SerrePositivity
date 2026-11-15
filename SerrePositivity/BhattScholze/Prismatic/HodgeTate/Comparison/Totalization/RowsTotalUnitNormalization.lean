module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedCompletedRowsTotal

/-!
# 完備行の Tot 計算同型と元の標準単位

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

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- Tot の計算同型は元の各行の標準単位を保つ。 -/
@[reassoc] theorem rowsUnit_comp_restrictedCompletedRowsTotalIso {r : ℕ} (x : Fin r → R)
    (c : ℕ) (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n)) :
    DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (finiteCompletionRowsUnit x (tensorRows L.complex K))) ≫
        (L.restrictedCompletedRowsTotalIso x c hf K b hK hFlat).hom =
      DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (L.toRestrictedCompletedRows x K)) := by
  haveI := total_map_quasiIso_of_rows
    (finiteCompletionRowsUnit x (restrictedCompletedBaseChangeRows f x K)) (b-(c : ℤ))
    (L.restrictedCompletedRows_lowerBound x c hf K b hK hFlat)
    (L.completedRestrictedRows_lowerBound x c hf K b hK hFlat)
    (restrictedRowsUnit_quasiIso (f := f) x K)
  have h := congrArg (fun g => DerivedCategory.Q.map
    ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))
    (finiteCompletionRowsUnit_naturality x (L.toRestrictedCompletedRows x K))
  simp only [Functor.map_comp] at h
  dsimp only [restrictedCompletedRowsTotalIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, completedToRestrictedRows]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
