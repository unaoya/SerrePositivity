module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialResolutionNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeModelComparisonNaturality

/-!
# 元の S 線形完備導来比較の余単体的自然性

## 概要
元の入力の射を、標準の導来源と同じ厳密な S 完備行模型へ施した四角形を示す。

## 方針
二つの指定増大、K-flat 模型の計算同型、標準 S 比較、交代余面の自然性を合成する。

## 規約
下界は X と Y のそれぞれの元のホモロジーの下界でよい。

## 使われ方
BS 著者版 Lemma 4.22 の自然な完備導来底変換–Tot 比較。
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

/-- 元の入力の射を、同じ S 完備行の厳密な模型へ施す。 -/
def resolvedCompletedCosimplicialMap (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    resolvedCompletedBaseChange f x X ⟶ resolvedCompletedBaseChange f x Y :=
  Functor.whiskerRight (resolvedCosimplicialMap g)
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      finiteCompletionFunctor (fun j => f (x j)))

/-- 元の S 完備導来比較は、全ての厳密な余単体的入力の射について自然である。 -/
@[reassoc] theorem cosimplicialNativeCompletedBaseChangeComparison_naturality
    (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) (bX bY : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < bX → IsZero ((X.obj ⦋n⦌).homology i))
    (hY : ∀ n : ℕ, ∀ i : ℤ, i < bY → IsZero ((Y.obj ⦋n⦌).homology i)) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).map
        ((complexDerivedExtension f).map (DerivedCategory.Q.map (cosimplicialTotalMap g))) ≫
          cosimplicialNativeCompletedBaseChangeComparison f x Y bY hY =
      cosimplicialNativeCompletedBaseChangeComparison f x X bX hX ≫
        DerivedCategory.Q.map (cosimplicialTotalMap (resolvedCompletedCosimplicialMap f x g)) := by
  have hs := nativeCompletedScalarModelIso_naturality f x
    (resolvedTotalModelAugmentation X) (resolvedTotalModelAugmentation_quasiIso X bX hX)
    (complexResolutionFunctor_kFlat R _) (resolvedTotalModelAugmentation Y)
    (resolvedTotalModelAugmentation_quasiIso Y bY hY) (complexResolutionFunctor_kFlat R _)
    (cosimplicialTotalMap g) (resolvedTotalModelMap g) (resolvedTotalModelAugmentation_naturality g)
  have hc := finiteCompletedBaseChangeModelComparison_naturality f x
    ((alternatingCofaceMapComplex (Complex R)).map (resolvedCosimplicialMap g))
    ((complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial X)))
    ((complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial Y)))
    (resolvedTotalModelMap g)
    ((complexResolutionAugmentation R).naturality (resolvedCosimplicialTotalMap g)).symm
  have ha := (alternatingCofaceFunctorIso
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      finiteCompletionFunctor (fun j => f (x j)))).hom.naturality (resolvedCosimplicialMap g)
  change (standardCompletedRowsFunctor f x).map
      ((alternatingCofaceMapComplex (Complex R)).map (resolvedCosimplicialMap g)) ≫
        (resolvedCompletedRowsIso f x Y).hom =
      (resolvedCompletedRowsIso f x X).hom ≫
        (alternatingCofaceMapComplex (Complex S)).map (resolvedCompletedCosimplicialMap f x g) at ha
  have haQ := congrArg (fun k => DerivedCategory.Q.map
    ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map k)) ha
  simp only [Functor.map_comp, standardCompletedRowsFunctor, Functor.comp_map] at haQ
  dsimp only [cosimplicialNativeCompletedBaseChangeComparison]
  rw [reassoc_of% hs, reassoc_of% hc]
  simp only [Functor.mapIso_hom, cosimplicialTotalMap]
  rw [haQ]
  simp only [Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
