module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineBaseCohomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.HomologyCoefficientClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineBaseCohomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineOrdinaryRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialComparison
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all Mathlib.CategoryTheory.Iso
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap

/-!
# 元の affine 係数ホモロジー同型の余輪体上の値

## 概要
元の基底複体の係数同型が、元の剰余模型の同じコホモロジー類を運ぶことを示す。

## 方針
通常係数射の単位純テンソルの値と、核・ホモロジー射影の保存式を使う。

## 規約
元の Čech 係数射、元の交代余面複体、元の mapHomologyIso を使う。

## 使われ方
特定の Zp 係数変更で、標準 HT 写像との可換式を同じ類で検査する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped TensorProduct Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 同じ剰余模型の加法的なコホモロジーと元の基底複体のホモロジーの指定同型。 -/
def affineNativeBaseCohomologyEquiv (i : ℕ) :
    hodgeTateCohomology' P hP r i ≃+ (affineBaseComplex P hP r).homology i :=
  cohomologyEquivModuleHomology A (reducedModel P hP r) (affineBaseCoefficients P hP r) i

/-- 元の剰余余輪体を、元の基底複体の同じ余輪体として読む。 -/
def affineNativeBaseCycleRep (i : ℕ) (c : Cocycles (reducedModel P hP r) i) :
    (affineBaseComplex P hP r).cycles i :=
  moduleCycleRep A (reducedModel P hP r) (affineBaseCoefficients P hP r) i c

/-- この指定同型は、同じ余輪体の同じホモロジー類を取る。 -/
theorem affineNativeBaseCohomologyEquiv_class (i : ℕ)
    (c : Cocycles (reducedModel P hP r) i) :
    affineNativeBaseCohomologyEquiv P hP r i (cohomologyClass _ i c) =
      (affineBaseComplex P hP r).homologyπ i
        (affineNativeBaseCycleRep P hP r i c) :=
  cohomologyEquivModuleHomology_class A (reducedModel P hP r) (affineBaseCoefficients P hP r) i c

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))

/-- 元の通常係数射は、単位純テンソル上で元の剰余係数射を与える。 -/
theorem affineCrystallineOrdinaryCoefficientMap_one_tmul (n : SimplexCategory)
    (x : (affineBaseModules P hP r).obj n) :
    letI := f.toRingHom.toAlgebra
    (affineCrystallineOrdinaryCoefficientMap f hP hQ hPg hQg r).app n ((1 : B) ⊗ₜ[A] x) =
      (affineHTCoefficientReduced f hP hQ r (crystallineCoefficientGenerator_eq f hPg hQg)).app n x := by
  letI := f.toRingHom.toAlgebra
  have h := completedCoefficientMap_unit p A B (reducedModel P hP r) (reducedModel Q hQ r)
      (affineBaseCoefficients P hP r) (affineBaseCoefficients Q hQ r)
      (affineHTCoefficientReduced f hP hQ r (crystallineCoefficientGenerator_eq f hPg hQg))
      (affineBaseCoefficient_square hP r f hQ (crystallineCoefficientGenerator_eq f hPg hQg))
      (affineBaseModules_complete Q hQ r) n 1 x
  dsimp only [affineCrystallineOrdinaryCoefficientMap, Functor.whiskerLeft_app,
    NatTrans.comp_app, ConcreteCategory.comp_apply, affineBaseCompletedCoefficientMap,
    pCompletedScalarExtensionFunctor, affineBaseModules, Functor.comp_obj] at h ⊢
  convert! h using 1 <;>
    simp only [coefficientTermFunction, one_smul, RingHom.algebraMap_toAlgebra]

/-- 元の基底複体の指定同型も、各次数で同じ単位純テンソルの値を持つ。 -/
theorem affineCrystallineBaseComplexIso_one_tmul (i : ℕ)
    (x : (affineBaseComplex P hP r).X i) :
    letI := f.toRingHom.toAlgebra
    (affineCrystallineBaseComplexIso f hP hQ hPg hQg r).hom.f i ((1 : B) ⊗ₜ[A] x) =
      (affineHTCoefficientReduced f hP hQ r (crystallineCoefficientGenerator_eq f hPg hQg)).app ⦋i⦌ x := by
  letI := f.toRingHom.toAlgebra
  change (affineCrystallineOrdinaryCoefficientMap f hP hQ hPg hQg r).app ⦋i⦌ ((1 : B) ⊗ₜ[A] x) = _
  exact affineCrystallineOrdinaryCoefficientMap_one_tmul hP r f hQ hPg hQg ⦋i⦌ x

set_option maxHeartbeats 800000 in
-- 元の行模型の係数作用とホモロジー比較の型を同時に照合する。
/-- 平坦な元の係数ホモロジー同型は、元のコホモロジー類を単位純テンソルから運ぶ。 -/
theorem affineCrystallineBaseCohomologyIso_one_tmul (hf : f.toRingHom.Flat) (i : ℕ)
    (z : hodgeTateCohomology' P hP r i) :
    letI := f.toRingHom.toAlgebra
    (affineCrystallineBaseCohomologyIso f hP hQ hPg hQg hf r i).hom
      ((1 : B) ⊗ₜ[A] affineNativeBaseCohomologyEquiv P hP r i z) =
      affineNativeBaseCohomologyEquiv Q hQ r i
        (cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r
          (crystallineCoefficientGenerator_eq f hPg hQg)) i z) := by
  letI := f.toRingHom.toAlgebra
  let F := ModuleCat.extendScalars f.toRingHom
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let K := affineBaseComplex P hP r
  let L := affineBaseComplex Q hQ r
  let KF := (F.mapHomologicalComplex (.up ℕ)).obj K
  let e := affineCrystallineBaseComplexIso f hP hQ hPg hQg r
  let q := affineHTCoefficientReduced f hP hQ r (crystallineCoefficientGenerator_eq f hPg hQg)
  obtain ⟨c, rfl⟩ := cohomologyClass_surjective (reducedModel P hP r) i z
  let cP := moduleCycleRep A (reducedModel P hP r) (affineBaseCoefficients P hP r) i c
  let cQ := moduleCycleRep B (reducedModel Q hQ r) (affineBaseCoefficients Q hQ r) i
    (cocycleMap _ _ q i c)
  let v := ((K.sc i).mapCyclesIso F).inv ((1 : B) ⊗ₜ[A] cP)
  have hi : KF.iCycles i v = (1 : B) ⊗ₜ[A] K.iCycles i cP := by
    have h := ConcreteCategory.congr_hom (coefficientCyclesIso_inv_inclusion (K.sc i) F)
      ((1 : B) ⊗ₜ[A] cP)
    change KF.iCycles i v = (1 : B) ⊗ₜ[A] K.iCycles i cP at h
    exact h
  have hv : HomologicalComplex.cyclesMap e.hom i v = cQ := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.hom i) v
    change L.iCycles i (HomologicalComplex.cyclesMap e.hom i v) = e.hom.f i (KF.iCycles i v) at h
    rw [h, hi, moduleCycleRep_apply, affineCrystallineBaseComplexIso_one_tmul,
      moduleCycleRep_apply]
    rfl
  have hp : ((K.sc i).mapHomologyIso F).inv ((1 : B) ⊗ₜ[A] K.homologyπ i cP) =
      KF.homologyπ i v := by
    have h := ConcreteCategory.congr_hom (coefficientHomologyIso_inv_projection (K.sc i) F)
      ((1 : B) ⊗ₜ[A] cP)
    change ((K.sc i).mapHomologyIso F).inv ((1 : B) ⊗ₜ[A] K.homologyπ i cP) =
      KF.homologyπ i v at h
    exact h
  rw [affineNativeBaseCohomologyEquiv_class, cohomologyMap_class,
    affineNativeBaseCohomologyEquiv_class]
  change HomologicalComplex.homologyMap e.hom i
    (((K.sc i).mapHomologyIso F).inv ((1 : B) ⊗ₜ[A] K.homologyπ i cP)) = L.homologyπ i cQ
  rw [hp]
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e.hom i) v
  change HomologicalComplex.homologyMap e.hom i (KF.homologyπ i v) =
    L.homologyπ i (HomologicalComplex.cyclesMap e.hom i v) at h
  exact h.trans (congrArg (L.homologyπ i) hv)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
