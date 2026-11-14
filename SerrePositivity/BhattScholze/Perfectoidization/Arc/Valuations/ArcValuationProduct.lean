module

public import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.Algebraic.Cardinality

/-!
## 概要
絶対整閉付値環の積による affine v 被覆（BM18 Proposition 3.30）。
## 方針
素点ごとの固定した代数閉分数体へ付値を引き戻し、代表の積から持ち上げる。
## 規約
添字・環は同じ宇宙。各代表の濃度は基底環の濃度と可算濃度の最大以下。
## 使われ方
完全環上の arc 被覆の Čech 完全性を絶対整閉付値環へ帰着する。
-/

@[expose] public noncomputable section

universe u

open _root_.CategoryTheory _root_.Cardinal
open scoped _root_.Cardinal

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

/-- 一射の affine v 被覆。任意の付値環からの試験を忠実平坦な付値環拡大で持ち上げる
（BS17 Definition 2.1、BM18 Proposition 3.30）。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsAffineVCover {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V] (k : A →+* V),
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : B →+* W),
        e.FaithfullyFlat ∧ l.comp f = e.comp k

variable (A : Type u) [CommRing A]

/-- 各素点に固定した代数閉分数体（BM18 Lemma 3.29 の代表系）。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField (P : PrimeSpectrum A) :=
  AlgebraicClosure (FractionRing (A ⧸ P.asIdeal))

/-- 基底環から素点に固定した代数閉分数体への射。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap (P : PrimeSpectrum A) : A →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A P :=
  (algebraMap (A ⧸ P.asIdeal) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A P)).comp
    (Ideal.Quotient.mk P.asIdeal)

/-- 基底環の像を含む、固定代数閉分数体の付値部分環の添字。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex :=
  Σ P : PrimeSpectrum A,
    {W : ValuationSubring (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A P) |
      ∀ a, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap A P a ∈ W}

/-- 代表付値環。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) : Type u := t.2.val

/-- 基底環から代表付値環への射。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeMap (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) : A →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t :=
  (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap A t.1).codRestrict t.2.val.toSubring t.2.property

/-- 各代表付値環は絶対整閉（BM18 Lemma 3.29）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbe_aic (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) :
    _root_.SerrePositivity.IsAbsolutelyIntegrallyClosed (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) :=
  _root_.SerrePositivity.valuationSubring_aic t.2.val

/-- 代表の濃度は基底環の濃度と可算濃度の最大以下（BM18 Lemma 3.29）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbe_cardinal_le (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) :
    #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) ≤ max #A ℵ₀ := by
  let K := FractionRing (A ⧸ t.1.asIdeal)
  let L := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A t.1
  have hQ : #(A ⧸ t.1.asIdeal) ≤ #A :=
    Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := t.1.asIdeal))
  have hK : #K ≤ #A := (Cardinal.mk_fractionRing _).le.trans hQ
  exact (Cardinal.mk_le_of_injective (f := (Subtype.val : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t → L))
    Subtype.val_injective).trans
    ((Algebra.IsAlgebraic.cardinalMk_le_max K L).trans (max_le_max_right _ hK))

/-- 絶対整閉付値環の代表族への積射。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProductMap : A →+* ∀ t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t :=
  RingHom.pi (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeMap A)

/-- 代数閉体の付値部分環への射は、小さい代表を経由する
（BM18 Lemma 3.29）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_valuationProbe_factor {L : Type u} [Field L] [IsAlgClosed L]
    (W : ValuationSubring L) (k : A →+* W) :
    ∃ (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) (i : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t →+* W),
      i.FaithfullyFlat ∧ i.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeMap A t) = k := by
  let f : A →+* L := (algebraMap W L).comp k
  let P : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  let : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (A ⧸ P.asIdeal)
  let : Field K := inferInstanceAs (Field (FractionRing (A ⧸ P.asIdeal)))
  let q : (A ⧸ P.asIdeal) →+* L := RingHom.kerLift f
  have hq : Function.Injective q := RingHom.kerLift_injective f
  let l₀ : K →+* L := IsFractionRing.lift (K := K) hq
  let : Algebra K L := l₀.toAlgebra
  let l₁ : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A P →ₐ[K] L := IsAlgClosed.lift
  have hcomm (a : A) : l₁ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap A P a) = f a := by
    change l₁ (algebraMap (A ⧸ P.asIdeal) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeField A P)
      (Ideal.Quotient.mk P.asIdeal a)) = f a
    rw [IsScalarTower.algebraMap_apply (A ⧸ P.asIdeal) K, l₁.commutes]
    change l₀ (algebraMap (A ⧸ P.asIdeal) K (Ideal.Quotient.mk P.asIdeal a)) = f a
    exact (IsFractionRing.lift_algebraMap (K := K) hq _).trans
      (RingHom.kerLift_mk f a)
  let W₀ := W.comap l₁.toRingHom
  have hW₀ (a : A) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap A P a ∈ W₀ := by
    change l₁ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeFieldMap A P a) ∈ W
    rw [hcomm]
    exact (k a).property
  let t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A := ⟨P, W₀, hW₀⟩
  let i : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t →+* W := _root_.SerrePositivity.valuationSubringComapHom W l₁.toRingHom
  refine ⟨t, i, _root_.SerrePositivity.valuationSubringComapHom_faithfullyFlat W l₁.toRingHom, ?_⟩
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact hcomm a

/-- 代表付値環の積への射は v 被覆（BM18 Proposition 3.30）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProduct_vCover : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsAffineVCover (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProductMap A) := by
  intro V _ _ k
  let L := AlgebraicClosure (FractionRing V)
  obtain ⟨W, hw, hflat⟩ := _root_.SerrePositivity.exists_valuationSubring_algebraicClosure V
  let e : V →+* W := (algebraMap V L).codRestrict W.toSubring hw
  obtain ⟨t, i, _, hi⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_valuationProbe_factor A W (e.comp k)
  let l := i.comp (Pi.evalRingHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A) t)
  exact ⟨CommRingCat.of W, inferInstance, inferInstance, e, l, hflat, hi⟩

/-- 基底が完全標数 p なら代表付値環の積も完全（BM18 Proposition 3.30 の完全環版）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeProduct_perfectRing (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    PerfectRing (∀ t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) p := by
  have ht (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) : PerfectRing (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) p := by
    have hpt : (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) = 0 := by
      rw [← map_natCast (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbeMap A t), hp, map_zero]
    let : CharP (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t) p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpt
    exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationProbe_aic A t).perfectRing_of_charP p
  have hF (t : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbeIndex A) :
      Function.Bijective (fun x : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.ValuationProbe A t => x ^ p) :=
    (ht t).bijective_frobenius
  exact ⟨Function.Bijective.piMap hF⟩

end SerrePositivity.BhattScholze.Perfectoidization.Derived
