module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
概要：指定区間環とスペクトルの閉区間を比較し、隣接点の次元と全区間の環を照合する。
方針：商と局所化の順序同型、区間環の同じ普遍性を使う。
規約：端点と元の構造射を保ち、新しい区間の選択をしない。
使われ方：2iのI01〜I03、BM18 Definition 4.6・Proposition 4.8(2)。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画I01：指定された端点の区間環との照合。 -/
def intervalRingSpectrumOrderIso {V : Type u} [CommRing V]
    {a b : PrimeSpectrum V} (h : a ≤ b) :
    PrimeSpectrum (ValuationIntervalRing h) ≃o Set.Icc a b := by
  let q : PrimeSpectrum (V ⧸ a.asIdeal) := ⟨intervalPrime h, inferInstance⟩
  let eQ : PrimeSpectrum (V ⧸ a.asIdeal) ≃o PrimeSpectrum.zeroLocus (R := V) (a.asIdeal : Set V) :=
    Ideal.primeSpectrumQuotientOrderIsoZeroLocus a.asIdeal
  have hq : (eQ q).val = b := PrimeSpectrum.ext (intervalPrime_comap h)
  let e : Set.Iic q ≃o Set.Icc a b :=
    { toFun := fun x ↦ ⟨(eQ x.val).val, (eQ x.val).property, by
        have he : (eQ x.val).val ≤ (eQ q).val := eQ.monotone x.property
        simpa only [hq] using he⟩
      invFun := fun y ↦ ⟨eQ.symm (⟨y.val, y.property.1⟩ : PrimeSpectrum.zeroLocus (R := V) (a.asIdeal : Set V)), by
        have he : (⟨y.val, y.property.1⟩ : PrimeSpectrum.zeroLocus (R := V) (a.asIdeal : Set V)) ≤ eQ q := by
          change y.val ≤ (eQ q).val
          rw [hq]
          exact y.property.2
        simpa using eQ.symm.monotone he⟩
      left_inv := by intro x; apply Subtype.ext; exact eQ.symm_apply_apply x.val
      right_inv := by
        intro y
        apply Subtype.ext
        change (eQ (eQ.symm (⟨y.val, y.property.1⟩ : PrimeSpectrum.zeroLocus (R := V) (a.asIdeal : Set V)))).val = y.val
        exact congrArg Subtype.val (eQ.apply_symm_apply ⟨y.val, y.property.1⟩)
      map_rel_iff' := by intro x y; exact eQ.le_iff_le }
  exact (IsLocalization.AtPrime.primeSpectrumOrderIso (ValuationIntervalRing h)
    (intervalPrime h)).trans e

/-- 計画I02：指定された端点の区間環との照合。 -/
theorem intervalRing_krullDim_le_one_of_no_prime_between
    {V : Type u} [CommRing V] {a b : PrimeSpectrum V} (h : a ≤ b)
    (hgap : ∀ c : PrimeSpectrum V, a ≤ c → c ≤ b → c = a ∨ c = b) :
    ringKrullDim (ValuationIntervalRing h) ≤ 1 := by
  let e := intervalRingSpectrumOrderIso h
  change Order.krullDim (PrimeSpectrum (ValuationIntervalRing h)) ≤ 1
  apply Order.krullDim_le_one_iff.mpr
  intro x
  rcases hgap (e x).val (e x).property.1 (e x).property.2 with hx | hx
  · left
    intro y hy
    apply e.le_iff_le.mp
    change (e x).val ≤ (e y).val
    rw [hx]
    exact (e y).property.1
  · right
    intro y hy
    apply e.le_iff_le.mp
    change (e y).val ≤ (e x).val
    rw [hx]
    exact (e y).property.2

/-- 計画I03：指定された端点の区間環との照合。 -/
def intervalRingOfFullSpectrumEquiv {V : Type u} [CommRing V]
    [IsDomain V] [ValuationRing V] (a b : PrimeSpectrum V)
    (ha : a.asIdeal = ⊥) (hb : b.asIdeal = IsLocalRing.maximalIdeal V)
    (h : a ≤ b) : ValuationIntervalRing h ≃ₐ[V] V := by
  have hz (x : V) (hx : x ∈ a.asIdeal) : (RingHom.id V) x = 0 := by
    change x = 0
    have hx' : x ∈ (⊥ : Ideal V) := ha ▸ hx
    exact hx'
  have hu (x : V) (hx : x ∉ b.asIdeal) : IsUnit ((RingHom.id V) x) := by
    change IsUnit x
    have hx' : x ∉ IsLocalRing.maximalIdeal V := hb ▸ hx
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hx'
  let f := intervalRingLift h (RingHom.id V) hz hu
  let g := algebraMap V (ValuationIntervalRing h)
  have hfg : f.comp g = RingHom.id V := by
    apply RingHom.ext
    intro x
    exact intervalRingLift_algebraMap h (RingHom.id V) hz hu x
  have hgf : g.comp f = RingHom.id (ValuationIntervalRing h) := by
    apply intervalRing_hom_ext h
    intro x
    change g (f (algebraMap V (ValuationIntervalRing h) x)) = algebraMap V _ x
    rw [intervalRingLift_algebraMap]
    rfl
  exact { RingEquiv.ofRingHom f g hfg hgf with
    commutes' := fun x ↦ intervalRingLift_algebraMap h (RingHom.id V) hz hu x }

end SerrePositivity.AlgebraicGeometry.ArcRouteB
