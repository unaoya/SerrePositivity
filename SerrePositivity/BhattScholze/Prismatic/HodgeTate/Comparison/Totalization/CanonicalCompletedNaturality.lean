module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CanonicalCosimplicialComparison

/-!
# 元の模型を選ばない完備比較の自然性

## 概要
元の標準単位で指定した比較は、同じ行の複体の射について自然である。

## 方針
完備な終域への射の一意性で、元の導来増大と通常のTot比較の自然性へ戻す。

## 規約
行の複体にも射にも追加のK-flat性を要求しない。

## 使われ方
元の余単体的分解の増大を外し、実際の標準写像の比較を計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion SerrePositivity.HomologicalAlgebra
open SerrePositivity.DifferentialGraded.ScalarExtension
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の標準単位で定義した完備比較は、元の行の複体の射に関して自然。 -/
@[reassoc] theorem canonicalCompletedBaseChangeComparison_naturality
    (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).map
        ((complexDerivedExtension f).map (DerivedCategory.Q.map
          ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))) ≫
        canonicalCompletedBaseChangeComparison f x M =
      canonicalCompletedBaseChangeComparison f x K ≫ DerivedCategory.Q.map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
          ((standardCompletedRowsFunctor f x).map g)) := by
  let t := (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g
  apply finiteDerivedCompletionHom_ext (fun j => f (x j))
    ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K)))
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x M)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j))
      ((baseChangeRowsFunctor f).obj M))
  have hu := (finiteDerivedCompletionUnit (fun j => f (x j))).naturality
    ((complexDerivedExtension f).map (DerivedCategory.Q.map t))
  simp only [Functor.id_map] at hu
  rw [← Category.assoc, ← hu, Category.assoc,
    unit_comp_canonicalCompletedBaseChangeComparison,
    unit_comp_canonicalCompletedBaseChangeComparison_assoc]
  have hn := (complexDerivedExtensionAugmentation f).naturality t
  change (complexDerivedExtension f).map (DerivedCategory.Q.map t) ≫
      (complexDerivedExtensionAugmentation f).app (total M) =
    (complexDerivedExtensionAugmentation f).app (total K) ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map t) at hn
  rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg DerivedCategory.Q.map
    (baseChangeModelToCompletedRows_naturality f x g (𝟙 _) (𝟙 _) t
      (by simp only [Category.id_comp, Category.comp_id, t]))

open AlgebraicTopology HTComparisonResolution
open scoped Simplicial

/-- 元の余単体的分解の増大を完備した行へ写すと、模型を選ばない比較へ戻る。 -/
theorem cosimplicialNativeComparison_comp_augmentation
    (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → CategoryTheory.Limits.IsZero ((X.obj ⦋n⦌).homology i)) :
    cosimplicialNativeCompletedBaseChangeComparison f x X b hX ≫
        DerivedCategory.Q.map ((alternatingCofaceMapComplex (Complex S) ⋙
          cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
          (Functor.whiskerRight (resolvedCosimplicialAugmentation X)
            ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
              finiteCompletionFunctor (fun j => f (x j))))) =
      canonicalCompletedBaseChangeComparison f x
        ((alternatingCofaceMapComplex (Complex R)).obj X) ≫
          DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
            ((alternatingCofaceFunctorIso
              ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
                finiteCompletionFunctor (fun j => f (x j)))).app X).hom) := by
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
    finiteCompletionFunctor (fun j => f (x j))
  let AR := alternatingCofaceMapComplex (Complex R)
  let AS := alternatingCofaceMapComplex (Complex S)
  let T := cochainProductTotalizationFunctor (ModuleCat.{u} S)
  let a := resolvedCosimplicialAugmentation X
  have hn := ((alternatingCofaceFunctorIso E).hom.naturality a)
  have hn' := congrArg (fun k => DerivedCategory.Q.map (T.map k)) hn
  simp only [Functor.map_comp] at hn'
  apply (cancel_epi (resolvedTotalCompletedDerivedIso f x X b hX).hom).mp
  rw [cosimplicialNativeComparison_eq_canonical]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hcan := canonicalCompletedBaseChangeComparison_naturality f x (AR.map a)
  change (resolvedTotalCompletedDerivedIso f x X b hX).hom ≫
      canonicalCompletedBaseChangeComparison f x (AR.obj X) =
    canonicalCompletedBaseChangeComparison f x (AR.obj (resolvedCosimplicial X)) ≫
      DerivedCategory.Q.map (T.map ((standardCompletedRowsFunctor f x).map (AR.map a))) at hcan
  rw [reassoc_of% hcan]
  exact congrArg (fun k => canonicalCompletedBaseChangeComparison f x
    (AR.obj (resolvedCosimplicial X)) ≫ k) hn'.symm

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
