module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcCechUltraproduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：超積の族により、全ての完全係数上でČech完全性を検出する。
方針：係数T上のホモロジーを平坦底変換し、元の積環の加群の零性判定へ戻す。
規約：個々の超積の忠実平坦性や終域の完全性を仮定しない。
使われ方：2iのP01、BM18 Lemma 3.25の係数付きの適用。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画P01：超積の族による、全ての完全係数上のČech完全性の検出。 -/
theorem perfectRingCechUniversalExact_of_ultraproducts
    (p : ℕ) [Fact p.Prime] {ι : Type u} (R : ι → Type u)
    [∀ i, CommRing (R i)] [PerfectRing (∀ i, R i) p]
    [∀ U : Ultrafilter ι, PerfectRing (RingUltraproduct R U) p]
    {B : Type u} [CommRing B] (hp : (p : ∀ i, R i) = 0)
    (f : (∀ i, R i) →+* B)
    (hU : ∀ U : Ultrafilter ι, PerfectRingCechUniversalExact p
      (arcBaseChangeHom f (algebraMap (∀ i, R i) (RingUltraproduct R U)))) :
    PerfectRingCechUniversalExact p f := by
  intro T _ _ k
  let A := ∀ i, R i
  letI := f.toAlgebra
  letI := k.toAlgebra
  let BT := Under.mk (CommRingCat.ofHom (arcBaseChangeHom f k))
  apply (Cech.moduleCech_acyclic_iff BT).mp
  intro n
  let K := Cech.moduleCech BT
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let M := K.homology n
  letI : Module A M := Module.compHom M k
  letI : IsScalarTower A T M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply subsingleton_of_ultraproduct_tensor R M
  intro U
  let D := RingUltraproduct R U
  let TD := T ⊗[A] D
  letI : PerfectRing TD p := perfectTensor_of_primeCast_eq_zero p A T D hp
  letI : IsLocalization (ultrafilterDenominators R U) D := isLocalization_ringUltraproduct R U
  letI : Module.Flat A D := IsLocalization.flat D (ultrafilterDenominators R U)
  letI : Module.Flat T TD := inferInstance
  let iD : D →+* TD := (Algebra.TensorProduct.includeRight : D →ₐ[A] TD).toRingHom
  let iT : T →+* TD := algebraMap T TD
  let u : A →+* TD := algebraMap A TD
  have hiD : iD.comp (algebraMap A D) = u := RingHom.ext
    (Algebra.TensorProduct.includeRight : D →ₐ[A] TD).commutes
  have hiT : iT.comp k = u := RingHom.ext fun a ↦
    (IsScalarTower.algebraMap_apply A T TD a).symm
  let eD := arcBaseChangeTransIso f (algebraMap A D) iD u hiD
  let eT := arcBaseChangeTransIso f k iT u hiT
  have hd := (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso eD)).mpr (hU U TD iD)
  have ht := (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso eT)).mp hd
  have hn := (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso (arcBaseChangeArrowIso BT TD))).mp ht
  let F := tensorLeft (ModuleCat.of T TD)
  let eh := (K.sc n).mapHomologyIso F
  have hK := (Arc.cechExact_baseChange_iff_tensorCochain BT TD).mp hn n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK
  have hsub : Subsingleton (TD ⊗[T] M) :=
    ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso eh.symm)
  let e : (TD ⊗[T] M) ≃ₗ[A] (D ⊗[A] M) :=
    ((TensorProduct.comm T TD M).restrictScalars A).trans
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange A T T M D).restrictScalars A).trans
        (TensorProduct.comm A M D))
  letI := hsub
  exact e.symm.toEquiv.subsingleton

end SerrePositivity.AlgebraicGeometry.ArcRouteB
