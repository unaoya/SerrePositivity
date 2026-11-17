module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialResolvedModels
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardModelComparisonIso

/-!
# 標準の完備導来底変換と余単体的 Tot

## 概要
任意の厳密な余単体的複体の、元の S 線形完備導来底変換の比較を指定する。

## 方針
同じ半自由関手で行を解消し、元の Tot への増大と標準の導来底変換の増大を使う。

## 規約
入力の各行や Tot の K-flat 性は仮定しない。終点の厳密な S 行模型も元の導来図式と同定する。

## 使われ方
BS 著者版 Lemma 4.22 の有限完全 Tor 振幅と一様下界を持つ場合。
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

/-- 任意の指定 K-flat 分解で計算する、同じ S 完備導来底変換の源。 -/
def nativeCompletedScalarModelIso (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj ((finiteCompletionFunctor (fun j => f (x j))).obj (baseChange f P)) :=
  (finiteDerivedCompletionFunctor (fun j => f (x j))).mapIso (nativeDerivedScalarModelIso f q hq hP) ≪≫
    (finiteDerivedCompletionComparison (fun j => f (x j))).app (baseChange f P)

/-- 各項の標準 S 完備導来底変換を計算する厳密な余単体的模型。 -/
abbrev resolvedCompletedBaseChange (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) : CosimplicialObject (Complex S) :=
  resolvedCosimplicial X ⋙
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      finiteCompletionFunctor (fun j => f (x j)))

/-- 厳密な標的模型は、元の導来係数拡大と完備化の余単体的図式を計算する。 -/
def resolvedCompletedBaseChangeDerivedIso (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) :
    ((X ⋙ DerivedCategory.Q) ⋙ complexDerivedExtension f) ⋙
        finiteDerivedCompletionFunctor (fun j => f (x j)) ≅
      resolvedCompletedBaseChange f x X ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (resolvedCosimplicialDerivedIso f X)
      (finiteDerivedCompletionFunctor (fun j => f (x j))) ≪≫
    Functor.isoWhiskerLeft
      (resolvedCosimplicial X ⋙ (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ))
      (finiteDerivedCompletionComparison (fun j => f (x j)))

/-- 完備化した元の行複体と、同じ S 余単体的模型の交代余面複体の同型。 -/
def resolvedCompletedRowsIso (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) :
    standardCompletedBaseChangeRows f x
        ((alternatingCofaceMapComplex (Complex R)).obj (resolvedCosimplicial X)) ≅
      (alternatingCofaceMapComplex (Complex S)).obj (resolvedCompletedBaseChange f x X) :=
  (alternatingCofaceFunctorIso
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      finiteCompletionFunctor (fun j => f (x j)))).app (resolvedCosimplicial X)

/-- 元の Tot へ向かう、同じ K-flat 源の二つの増大の合成。 -/
def resolvedTotalModelAugmentation (X : CosimplicialObject (Complex R)) :
    (complexResolutionFunctor R).obj (cosimplicialTotal (resolvedCosimplicial X)) ⟶ cosimplicialTotal X :=
  (complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial X)) ≫
    resolvedCosimplicialTotalAugmentation X

/-- 元の行の一様下界により、同じ Tot 模型の増大は擬同型である。 -/
theorem resolvedTotalModelAugmentation_quasiIso (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    QuasiIso (resolvedTotalModelAugmentation X) := by
  haveI := complexResolutionAugmentation_quasiIso R (cosimplicialTotal (resolvedCosimplicial X))
  haveI := resolvedCosimplicialTotalAugmentation_quasiIso X b hX
  dsimp only [resolvedTotalModelAugmentation]
  infer_instance

/-- 元の標準単位と指定増大だけからなる S 線形完備導来比較。 -/
def cosimplicialNativeCompletedBaseChangeComparison (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ⟶
      DerivedCategory.Q.obj (cosimplicialTotal (resolvedCompletedBaseChange f x X)) :=
  (nativeCompletedScalarModelIso f x (resolvedTotalModelAugmentation X)
    (resolvedTotalModelAugmentation_quasiIso X b hX)
    (complexResolutionFunctor_kFlat R _)).hom ≫
  finiteCompletedBaseChangeModelComparison f x
    ((alternatingCofaceMapComplex (Complex R)).obj (resolvedCosimplicial X))
    ((complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial X))) ≫
  DerivedCategory.Q.map
    ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).mapIso (resolvedCompletedRowsIso f x X)).hom

/-- 有限完全 Tor 振幅と元の行の一様下界の下で、同じ標準 S 線形比較は同型となる。 -/
theorem cosimplicialNativeCompletedBaseChangeComparison_isIso (f : R →+* S) {r : ℕ}
    (x : Fin r → R) (c : ℕ) (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    IsIso (cosimplicialNativeCompletedBaseChangeComparison f x X b hX) := by
  haveI := (scalarResolution f).standardCompletedModelComparison_isIso x c hf
    ((alternatingCofaceMapComplex (Complex R)).obj (resolvedCosimplicial X)) b
    (resolvedCosimplicial_lowerBound X b hX) (fun n => resolvedCosimplicial_kFlat X ⦋n⦌)
    ((complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial X)))
    (complexResolutionAugmentation_quasiIso R _) (complexResolutionFunctor_kFlat R _)
  dsimp only [cosimplicialNativeCompletedBaseChangeComparison]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
