module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCanonicalComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeModelComparisonNaturality

/-!
# 余単体的比較の源の模型を外した表示

## 概要
元の入力への Tot 増大と、標準単位で指定した比較だけで同じ S 線形比較を表す。

## 方針
元の導来関手で写した Tot 増大を逆にし、模型を選ばない比較へ合成する。

## 規約
任意の源の K-flat 模型は既存の標準単位の一意性により同じ射を計算する。

## 使われ方
BS 著者版 Lemma 4.22 の比較射の計算模型への非依存。
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

/-- 元の Tot 増大を標準の完備導来底変換で写した同型。 -/
def resolvedTotalCompletedDerivedIso (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (cosimplicialTotal (resolvedCosimplicial X)))) ≅
      (finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) := by
  haveI := resolvedCosimplicialTotalAugmentation_quasiIso X b hX
  exact asIso ((finiteDerivedCompletionFunctor (fun j => f (x j))).map
    ((complexDerivedExtension f).map (DerivedCategory.Q.map (resolvedCosimplicialTotalAugmentation X))))

/-- 同じ余単体的比較は、源の模型を使わない標準の表示に一致する。 -/
theorem cosimplicialNativeComparison_eq_canonical (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    cosimplicialNativeCompletedBaseChangeComparison f x X b hX =
      (resolvedTotalCompletedDerivedIso f x X b hX).inv ≫
        canonicalCompletedBaseChangeComparison f x
          ((alternatingCofaceMapComplex (Complex R)).obj (resolvedCosimplicial X)) ≫
        DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).mapIso
          (resolvedCompletedRowsIso f x X)).hom := by
  let P := (complexResolutionFunctor R).obj (cosimplicialTotal (resolvedCosimplicial X))
  let q := (complexResolutionAugmentation R).app (cosimplicialTotal (resolvedCosimplicial X))
  have hq : QuasiIso q := complexResolutionAugmentation_quasiIso R _
  have hP : complexKFlat R P := complexResolutionFunctor_kFlat R _
  have hs := nativeCompletedScalarModelIso_naturality f x q hq hP
    (resolvedTotalModelAugmentation X) (resolvedTotalModelAugmentation_quasiIso X b hX) hP
    (resolvedCosimplicialTotalAugmentation X) (𝟙 P)
    (by exact (Category.id_comp (q ≫ resolvedCosimplicialTotalAugmentation X)).symm)
  rw [((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map_id P,
    (finiteCompletionFunctor (fun j => f (x j))).map_id
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P),
    DerivedCategory.Q.map_id ((finiteCompletionFunctor (fun j => f (x j))).obj
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P))] at hs
  have hs' := hs.trans (Category.comp_id (nativeCompletedScalarModelIso f x q hq hP).hom)
  apply (cancel_epi (resolvedTotalCompletedDerivedIso f x X b hX).hom).mp
  dsimp only [cosimplicialNativeCompletedBaseChangeComparison]
  change (resolvedTotalCompletedDerivedIso f x X b hX).hom ≫
      ((nativeCompletedScalarModelIso f x (resolvedTotalModelAugmentation X)
        (resolvedTotalModelAugmentation_quasiIso X b hX) hP).hom ≫ _) = _
  change (finiteDerivedCompletionFunctor (fun j => f (x j))).map
      ((complexDerivedExtension f).map (DerivedCategory.Q.map (resolvedCosimplicialTotalAugmentation X))) ≫
        _ = _
  rw [reassoc_of% hs', reassoc_of% (nativeCompletedComparison_eq_canonical f x
    ((alternatingCofaceMapComplex (Complex R)).obj (resolvedCosimplicial X)) q hq hP)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
