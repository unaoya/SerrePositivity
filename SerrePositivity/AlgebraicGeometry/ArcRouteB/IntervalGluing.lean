module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalOverlap
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：重なる区間の三つの底変換で、任意の完全係数の増大Čech完全性を検出する。
方針：L01/L02で同じArrowを保って係数を比較し、T上の短完全列とTor消滅をmoduleCechへ適用する。
規約：係数Tの平坦性は仮定しない。単なる完全性を非平坦底変換へ保存したことにしない。
使われ方：2iのO06、BM18 Proposition 4.8(5)の構造層に特殊化した普遍貼り合わせ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O09：同じVの重なる二つの良い区間を貼り合わせる。 -/
theorem goodArcInterval_glue (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing B] [PerfectRing V p] [PerfectRing B p] (hp : (p : V) = 0)
    (f : V →+* B) {a b c d : PrimeSpectrum V} (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) (h₁ : GoodArcInterval p f a b) (h₂ : GoodArcInterval p f c d) :
    GoodArcInterval p f a d := by
  intro had T _ _ k
  let R := ValuationIntervalRing had
  let vR : V →+* R := algebraMap V R
  let vT := k.comp vR
  letI := f.toAlgebra
  letI : Algebra R T := k.toAlgebra
  letI : Algebra V T := vT.toAlgebra
  letI : IsScalarTower V R T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let kV : R →ₐ[V] T := { toRingHom := k, commutes' := fun _ ↦ rfl }
  let BT := Under.mk (CommRingCat.ofHom (arcBaseChangeHom f vT))
  letI : PerfectRing BT.right p := perfectTensor_of_primeCast_eq_zero p V T B hp
  have transfer (E D : Type u) [CommRing E] [Algebra V E] [PerfectRing E p]
      [CommRing D] [Algebra V D] [PerfectRing D p] [Algebra T D] [IsScalarTower V T D]
      (e : E →ₐ[V] D)
      (he : PerfectRingCechUniversalExact p (arcBaseChangeHom f (algebraMap V E))) :
      Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
        (CommRingCat.of D)).obj BT).hom) := by
    let u : V →+* D := algebraMap V D
    let iT : T →+* D := algebraMap T D
    have heV : e.toRingHom.comp (algebraMap V E) = u := RingHom.ext e.commutes
    have hiT : iT.comp vT = u := RingHom.ext fun v ↦
      (IsScalarTower.algebraMap_apply V T D v).symm
    let eE := arcBaseChangeTransIso f (algebraMap V E) e.toRingHom u heV
    let eT := arcBaseChangeTransIso f vT iT u hiT
    have hd := (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso eE)).mpr (he D e.toRingHom)
    have ht := (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso eT)).mp hd
    exact (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso (arcBaseChangeArrowIso BT D))).mp ht
  let hab := hac.trans hcb
  let hcd := hcb.trans hbd
  let L := Localization.AtPrime b.asIdeal
  let Q := V ⧸ c.asIdeal
  let I := ValuationIntervalRing hcb
  letI : PerfectRing L p := intervalCoefficient_primeLocalization_perfect p hp b
  letI : PerfectRing Q p := intervalCoefficient_primeQuotient_perfect p hp c
  letI : PerfectRing I p := perfectRing_interval hcb p hp
  letI : PerfectRing (ValuationIntervalRing hab) p := perfectRing_interval hab p hp
  letI : PerfectRing (ValuationIntervalRing hcd) p := perfectRing_interval hcd p hp
  letI : PerfectRing (T ⊗[V] L) p := perfectTensor_of_primeCast_eq_zero p V T L hp
  letI : PerfectRing (T ⊗[V] Q) p := perfectTensor_of_primeCast_eq_zero p V T Q hp
  letI : PerfectRing (T ⊗[V] I) p := perfectTensor_of_primeCast_eq_zero p V T I hp
  let el : ValuationIntervalRing hab →ₐ[V] T ⊗[V] L :=
    (Algebra.TensorProduct.map kV (AlgHom.id V L)).comp
      (intervalTensorLocalizationEquiv hab hbd).symm.toAlgHom
  let eq : ValuationIntervalRing hcd →ₐ[V] T ⊗[V] Q :=
    (Algebra.TensorProduct.map kV (AlgHom.id V Q)).comp
      (intervalTensorQuotientEquiv hac hcd).symm.toAlgHom
  let ei : I →ₐ[V] T ⊗[V] I :=
    (Algebra.TensorProduct.map kV (AlgHom.id V I)).comp
      (intervalTensorIntersectionEquiv hac hcb hbd).symm.toAlgHom
  have hi : GoodArcInterval p f c b := goodArcInterval_sub p f h₁ hac hcb le_rfl
  have hdirect := cechExact_of_overlapTensor_coefficients p BT hp hcb
    (transfer _ _ el (h₁ hab)) (transfer _ _ eq (h₂ hcd)) (transfer _ _ ei (hi hcb))
  let e := arcBaseChangeTransIso f vR k vT rfl
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso e)).mp hdirect

end SerrePositivity.AlgebraicGeometry.ArcRouteB
