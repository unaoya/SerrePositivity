module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedStandardComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RowsTotalUnitNormalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedTotalComparisonIso
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-!
# K-flat 行模型での元の S 完備比較の同型性

## 概要
同じ標準 S 線形比較は、一様な行の下界と有限完全 Tor 振幅の下で同型となる。

## 方針
源と標的の指定 R 模型の単位を照合し、既に証明した R 完備比較の同型性を移す。

## 規約
任意の非有界入力の K-flat 性は要求しない。この段は実際の K-flat 行模型について述べる。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な余単体的入力への接続。
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
include L

/-- 制限した標準比較と R 完備比較は、元の合成単位によって同じ射と判定される。 -/
theorem restrictedStandardComparison_eq {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n))
    {P : Complex R} (q : P ⟶ total K) (hP : complexKFlat R P) :
    (L.restrictedCompletedSourceIso x P hP).hom ≫
      restrictedStandardCompletedComparison f x K q =
    DerivedCategory.Q.map ((finiteCompletionFunctor x).map (L.tensorFunctor.map q)) ≫
      finiteCompletedTensorTotalComparison x L.complex K ≫
        (L.restrictedCompletedRowsTotalIso x c hf K b hK hFlat).hom := by
  apply finiteCompletionHom_ext x (L.tensorFunctor.obj P)
    (DerivedCategory.Q.obj (total (restrictedCompletedBaseChangeRows f x K)))
    (fun j => total_isComplete (x j) (restrictedCompletedBaseChangeRows f x K)
      (fun n => restrictedCompletedBaseChangeRows_isComplete f x K n j))
  rw [← Category.assoc, unit_comp_restrictedCompletedSourceIso,
    source_comp_restrictedStandardCompletedComparison]
  have hu := congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality x (L.tensorFunctor.map q))
  simp only [Functor.map_comp] at hu
  rw [← reassoc_of% hu]
  change DerivedCategory.Q.map (L.tensorFunctor.map q ≫ tensorTotalComparison L.complex K ≫
      (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (L.toRestrictedCompletedRows x K)) =
    DerivedCategory.Q.map (L.tensorFunctor.map q) ≫
      DerivedCategory.Q.map (finiteCompletionUnit x (cochainTensor L.complex (total K))) ≫
        finiteCompletedTensorTotalComparison x L.complex K ≫
          (L.restrictedCompletedRowsTotalIso x c hf K b hK hFlat).hom
  rw [unit_comp_finiteCompletedTensorTotalComparison_assoc x L.complex K]
  dsimp only [tensorToFiniteCompletedRows]
  simp only [Functor.map_comp, Category.assoc]
  rw [rowsUnit_comp_restrictedCompletedRowsTotalIso L x c hf K b hK hFlat]

/-- 実際の K-flat 行模型での、元の標準 S 完備比較の同型性。 -/
theorem standardCompletedModelComparison_isIso {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hFlat : ∀ n : ℕ, complexKFlat R (K.X n))
    {P : Complex R} (q : P ⟶ total K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    IsIso (finiteCompletedBaseChangeModelComparison f x K q) := by
  haveI := hq
  haveI := L.tensorFunctor_map_quasiIso q
  haveI := finiteCompletionFunctor_map_quasiIso x (L.tensorFunctor.map q)
  haveI := L.finiteCompletedTensorTotalComparison_isIso x c hf K b hK
  haveI : IsIso ((L.restrictedCompletedSourceIso x P hP).hom ≫
      restrictedStandardCompletedComparison f x K q) := by
    rw [L.restrictedStandardComparison_eq x c hf K b hK hFlat q hP]
    infer_instance
  haveI : IsIso (restrictedStandardCompletedComparison f x K q) :=
    IsIso.of_isIso_comp_left (L.restrictedCompletedSourceIso x P hP).hom _
  have h := (inferInstance : IsIso (restrictedStandardCompletedComparison f x K q))
  dsimp only [restrictedStandardCompletedComparison, derivedComplexRestrictionMap] at h
  haveI hRes : IsIso ((derivedRestrictScalars f).map
      (finiteCompletedBaseChangeModelComparison f x K q)) := by
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h
  exact isIso_of_reflects_iso (finiteCompletedBaseChangeModelComparison f x K q)
    (derivedRestrictScalars f)

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
