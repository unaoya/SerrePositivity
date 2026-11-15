module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ComplexResolutionFunctor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeDerivedScalarModels
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalQuasiIso

/-!
# 厳密な余単体的入力の同じ半自由行模型

## 概要
既存の同じ分解候補を余単体的入力へ関手として適用し、その後に交代余面を取る。

## 方針
行ごとの K-flat 性と増大の自然性を保ち、一様下界の下で Tot の擬同型を得る。

## 規約
非加法的な分解関手を水平の微分へ直接適用しない。

## 使われ方
BS 著者版 Lemma 4.22 の標準の導来底変換の S 線形行模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.DifferentialGraded.ScalarExtension
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 同じ分解関手を余単体的対象へ適用した厳密な行模型。 -/
def resolvedCosimplicial (X : CosimplicialObject (Complex R)) : CosimplicialObject (Complex R) :=
  X ⋙ complexResolutionFunctor R

/-- 元の入力への同じ指定増大。 -/
def resolvedCosimplicialAugmentation (X : CosimplicialObject (Complex R)) :
    resolvedCosimplicial X ⟶ X where
  app j := (complexResolutionAugmentation R).app (X.obj j)
  naturality _ _ g := (complexResolutionAugmentation R).naturality (X.map g)

/-- 各行の増大は本体の同じ擬同型である。 -/
theorem resolvedCosimplicialAugmentation_quasiIso
    (X : CosimplicialObject (Complex R)) (j : SimplexCategory) :
    QuasiIso ((resolvedCosimplicialAugmentation X).app j) :=
  complexResolutionAugmentation_quasiIso R (X.obj j)

/-- 各行は本体の半自由性によって K-flat である。 -/
theorem resolvedCosimplicial_kFlat (X : CosimplicialObject (Complex R)) (j : SimplexCategory) :
    complexKFlat R ((resolvedCosimplicial X).obj j) :=
  complexResolutionFunctor_kFlat R (X.obj j)

/-- 同じ行模型は元の一様なホモロジー下界を保つ。 -/
theorem resolvedCosimplicial_lowerBound (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero (((resolvedCosimplicial X).obj ⦋n⦌).homology i) := by
  intro n i hi
  haveI := resolvedCosimplicialAugmentation_quasiIso X ⦋n⦌
  exact (hX n i hi).of_iso (isoOfQuasiIsoAt ((resolvedCosimplicialAugmentation X).app ⦋n⦌) i)

/-- 指定した同じ積 Tot の、元の入力への増大。 -/
def resolvedCosimplicialTotalAugmentation (X : CosimplicialObject (Complex R)) :
    cosimplicialTotal (resolvedCosimplicial X) ⟶ cosimplicialTotal X :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
    ((alternatingCofaceMapComplex (Complex R)).map (resolvedCosimplicialAugmentation X))

/-- 一様下界の下で、同じ Tot の増大も擬同型である。 -/
theorem resolvedCosimplicialTotalAugmentation_quasiIso
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    QuasiIso (resolvedCosimplicialTotalAugmentation X) :=
  total_map_quasiIso_of_rows _ b (resolvedCosimplicial_lowerBound X b hX) hX
    (fun n => resolvedCosimplicialAugmentation_quasiIso X ⦋n⦌)

/-- この厳密な S 線形行模型は元の標準導来係数拡大の図式を計算する。 -/
def resolvedCosimplicialDerivedIso (f : R →+* S) (X : CosimplicialObject (Complex R)) :
    (X ⋙ DerivedCategory.Q) ⋙ complexDerivedExtension f ≅
      (resolvedCosimplicial X ⋙ (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents (fun j => nativeDerivedScalarModelIso f
    ((resolvedCosimplicialAugmentation X).app j)
    (resolvedCosimplicialAugmentation_quasiIso X j) (resolvedCosimplicial_kFlat X j)) (by
      intro j k g
      exact nativeDerivedScalarModelIso_naturality f
        ((resolvedCosimplicialAugmentation X).app j)
        (resolvedCosimplicialAugmentation_quasiIso X j) (resolvedCosimplicial_kFlat X j)
        ((resolvedCosimplicialAugmentation X).app k)
        (resolvedCosimplicialAugmentation_quasiIso X k) (resolvedCosimplicial_kFlat X k)
        (X.map g) ((resolvedCosimplicial X).map g)
        ((resolvedCosimplicialAugmentation X).naturality g).symm)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
