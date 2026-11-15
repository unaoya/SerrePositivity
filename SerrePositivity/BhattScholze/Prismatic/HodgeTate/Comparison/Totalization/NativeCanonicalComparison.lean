module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteDerivedReflection
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 標準完備導来比較の源の模型への非依存

## 概要
本体の導来係数拡大の標準増大から、模型を選ばずに元の完備比較を定義する。

## 方針
標準単位の Hom 同値で一意に延長し、任意の実際の K-flat 模型での計算と照合する。

## 規約
模型間の射の存在や持ち上げを追加の仮定にしない。

## 使われ方
BS 著者版 Lemma 4.22 の元の比較射の計算模型への非依存。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.DifferentialGraded.ScalarExtension
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 任意の指定 K-flat 模型の計算同型は、元の導来係数拡大の増大を保つ。 -/
@[reassoc] theorem nativeDerivedScalarModelIso_comp_augmentation (f : R →+* S)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (nativeDerivedScalarModelIso f q hq hP).hom ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) =
      (complexDerivedExtensionAugmentation f).app K := by
  haveI := hq
  apply (cancel_epi ((complexDerivedExtension f).map (DerivedCategory.Q.map q))).mp
  rw [← Category.assoc, derived_map_comp_nativeDerivedScalarModelIso]
  simpa only [complexDerivedExtensionKFlatIso, asIso_hom, Functor.comp_map, Functor.comp_obj, extension] using
    ((complexDerivedExtensionAugmentation f).naturality q).symm

/-- 完備した計算同型は、元の導来単位を元の複体単位へ写す。 -/
@[reassoc] theorem nativeCompletedScalarModelIso_unit (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (finiteDerivedCompletionUnit (fun j => f (x j))).app
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj K)) ≫
      (nativeCompletedScalarModelIso f x q hq hP).hom =
    (nativeDerivedScalarModelIso f q hq hP).hom ≫
      DerivedCategory.Q.map (finiteCompletionUnit (fun j => f (x j)) (baseChange f P)) := by
  have hn := (finiteDerivedCompletionUnit (fun j => f (x j))).naturality
    (nativeDerivedScalarModelIso f q hq hP).hom
  simp only [Functor.id_map] at hn
  dsimp only [nativeCompletedScalarModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hn, Category.assoc]
  simpa only [Category.assoc, Iso.app_hom] using congrArg
    (fun k => (nativeDerivedScalarModelIso f q hq hP).hom ≫ k)
    (finiteDerivedCompletionUnit_comparison (fun j => f (x j)) (baseChange f P))

/-- 本体の標準増大から元の標準単位に沿って延長する、模型を選ばない比較。 -/
def canonicalCompletedBaseChangeComparison (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) :
    (finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K))) ⟶
      DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)) :=
  (finiteDerivedCompletionHomEquiv (fun j => f (x j))
    ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K)))
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))).symm
      ((complexDerivedExtensionAugmentation f).app (total K) ≫
        DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 (total K))))

/-- 模型を選ばない比較も、元の標準単位との合成で標準増大へ戻る。 -/
@[reassoc] theorem unit_comp_canonicalCompletedBaseChangeComparison (f : R →+* S)
    {r : ℕ} (x : Fin r → R) (K : CochainComplex (Complex R) ℕ) :
    (finiteDerivedCompletionUnit (fun j => f (x j))).app
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K))) ≫
      canonicalCompletedBaseChangeComparison f x K =
    (complexDerivedExtensionAugmentation f).app (total K) ≫
      DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 (total K))) := by
  have h := (finiteDerivedCompletionHomEquiv (fun j => f (x j))
    ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K)))
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))).apply_symm_apply
      ((complexDerivedExtensionAugmentation f).app (total K) ≫
        DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K (𝟙 (total K))))
  simpa only [finiteDerivedCompletionHomEquiv_apply, canonicalCompletedBaseChangeComparison] using h

/-- 任意の実際の K-flat 源での計算が、模型を選ばない元の標準比較に一致する。 -/
theorem nativeCompletedComparison_eq_canonical (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R}
    (q : P ⟶ total K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (nativeCompletedScalarModelIso f x q hq hP).hom ≫ finiteCompletedBaseChangeModelComparison f x K q =
      canonicalCompletedBaseChangeComparison f x K := by
  apply finiteDerivedCompletionHom_ext (fun j => f (x j))
    ((complexDerivedExtension f).obj (DerivedCategory.Q.obj (total K)))
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))
  rw [← Category.assoc, nativeCompletedScalarModelIso_unit, Category.assoc,
    unit_comp_finiteCompletedBaseChangeModelComparison, unit_comp_canonicalCompletedBaseChangeComparison]
  have hr₀ : baseChangeModelToCompletedRows f x K (𝟙 (total K)) =
      baseChangeTotalComparison f K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K)) := by
    dsimp only [baseChangeModelToCompletedRows]
    rw [((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map_id (total K)]
    exact Category.id_comp _
  have hr : baseChangeModelToCompletedRows f x K q =
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q ≫
        baseChangeModelToCompletedRows f x K (𝟙 (total K)) := by
    rw [hr₀]
    rfl
  rw [hr, Functor.map_comp, ← Category.assoc, nativeDerivedScalarModelIso_comp_augmentation]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
