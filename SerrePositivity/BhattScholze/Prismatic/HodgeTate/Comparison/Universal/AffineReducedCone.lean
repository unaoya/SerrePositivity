module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
public import SerrePositivity.HomologicalAlgebra.ScalarConeModuleQuotient
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 元の full envelope と剰余行のスカラー錐

## 概要
元の full envelope 上での d 倍の短完全列から、同じ剰余行を導来スカラー錐として計算する。

## 方針
元の商写像を基底線形に読み、生成元の正則性と主イデアルの核を使う。

## 規約
通常の基底環の平坦性を仮定しない。元の包と元の商射をそのまま使う。

## 使われ方
Construction 6.1 の項ごとの full envelope の底変換から剰余模型への比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open Cosimplicial DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の full envelope の基底上の台加群。 -/
abbrev affineFullBaseModules : CosimplicialObject (ModuleCat.{u} A) :=
  toModules A (htRings P hP r) (htBase P hP r)

/-- 元の full envelope から元の剰余行への同じ線形商射。 -/
def affineFullBaseProjection : affineFullBaseModules P hP r ⟶ affineBaseModules P hP r :=
  toModulesMap A (htBase P hP r) (affineBaseCoefficients P hP r)
    (quotProjection (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r) 1) (by rfl)

/-- 元の d 倍と商射の合成は零。 -/
theorem affineFullBaseProjection_zero (n : SimplexCategory) :
    (P.generator • 𝟙 ((affineFullBaseModules P hP r).obj n)) ≫
      (affineFullBaseProjection P hP r).app n = 0 := by
  ext x
  change (htRings P hP r).obj n at x
  change Ideal.Quotient.mk (Ideal.span {htGenerator P hP r n ^ (1 : ℕ)})
    (htGenerator P hP r n * x) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [pow_one] using
    (Ideal.span {htGenerator P hP r n}).mul_mem_right x (Ideal.subset_span rfl)

/-- 元の d 倍と元の商射の短複体。 -/
abbrev affineFullBaseReduction (n : SimplexCategory) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (P.generator • 𝟙 ((affineFullBaseModules P hP r).obj n))
    ((affineFullBaseProjection P hP r).app n) (affineFullBaseProjection_zero P hP r n)

/-- 元の full envelope の生成元の正則性が、元の短複体の短完全性を与える。 -/
theorem affineFullBaseReduction_shortExact (n : SimplexCategory) :
    (affineFullBaseReduction P hP r n).ShortExact := by
  haveI : Mono (P.generator • 𝟙 ((affineFullBaseModules P hP r).obj n)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : (htRings P hP r).obj n => htGenerator P hP r n * x)
    exact htGenerator_regular P hP r n
  haveI : Epi ((affineFullBaseProjection P hP r).app n) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (Ideal.Quotient.mk (Ideal.span {htGenerator P hP r n ^ (1 : ℕ)}))
    exact Ideal.Quotient.mk_surjective
  refine ⟨?_⟩
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change (htRings P hP r).obj n at x
  change Ideal.Quotient.mk (Ideal.span {htGenerator P hP r n ^ (1 : ℕ)}) x = 0 at hx
  have hm : x ∈ Ideal.span {htGenerator P hP r n ^ (1 : ℕ)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  refine ⟨y, ?_⟩
  change htGenerator P hP r n * y = x
  simpa only [pow_one] using hy.symm

/-- 元の full envelope の d の導来錐は、同じ元の剰余行の零次数対象である。 -/
def affineReducedScalarConeIso (n : SimplexCategory) :
    (derivedScalarConeFunctor A P.generator).obj
        ((moduleObjectFunctor A).obj ((affineFullBaseModules P hP r).obj n)) ≅
      (moduleObjectFunctor A).obj ((affineBaseModules P hP r).obj n) := by
  let F := CochainComplex.singleFunctor (ModuleCat.{u} A) 0
  let S := (affineFullBaseReduction P hP r n).map F
  have hS : S.ShortExact := (affineFullBaseReduction_shortExact P hP r n).map_of_exact F
  haveI := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  exact (derivedScalarConeComparison A P.generator).app
      (F.obj ((affineFullBaseModules P hP r).obj n)) ≪≫
    eqToIso (by
      change DerivedCategory.Q.obj (CochainComplex.mappingCone
          (SerrePositivity.smulId P.generator (F.obj ((affineFullBaseModules P hP r).obj n)))) =
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          (F.map (P.generator • 𝟙 ((affineFullBaseModules P hP r).obj n))))
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl) ≪≫
    asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
