module

public import SerrePositivity.AlgebraicGeometry.ValuationProbeExtension
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
概要：付値整域上の忠実平坦な環へ、付値環の忠実平坦拡大を通る写像を作る。
方針：閉点上の素点と going-down の一般点を取り、局所環の体への射を付値部分環へ因子化する。
規約：有限型・有限表示・Noether 性は仮定しない。
使われ方：G0 の忠実平坦射の v 被覆判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing B]

/-- 付値整域上の忠実平坦射を、忠実平坦な付値整域の拡大へ持ち上げる。 -/
theorem exists_valuation_lift_of_faithfullyFlat (f : V →+* B) (hf : f.FaithfullyFlat) :
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : B →+* W),
        e.FaithfullyFlat ∧ l.comp f = e := by
  letI : Algebra V B := f.toAlgebra
  letI : Module.FaithfullyFlat V B := hf
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := B)
    ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
  letI : Q.asIdeal.IsPrime := Q.isPrime
  have hq : Q.asIdeal.comap f = IsLocalRing.maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQ
  letI : Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hq.symm⟩
  obtain ⟨P, hPQ, hP, hPv⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal V)) (q := IsLocalRing.maximalIdeal V) bot_le
  letI : P.IsPrime := hP
  letI : P.LiesOver (⊥ : Ideal V) := hPv
  let R := Localization.AtPrime Q.asIdeal
  let K := P.ResidueField
  let a : V →+* R := (algebraMap B R).comp f
  letI : IsLocalHom a := ((IsLocalRing.local_hom_TFAE a).out 5 1).mp (by
    change ((IsLocalRing.maximalIdeal R).comap (algebraMap B R)).comap f = _
    have hm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = Q.asIdeal :=
      IsLocalization.AtPrime.under_maximalIdeal R Q.asIdeal
    rw [hm]
    exact hq)
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (algebraMap B K y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hyP : (y : B) ∈ P := Ideal.algebraMap_residueField_eq_zero.mp hy
    exact y.property (hPQ hyP)
  let φ : R →+* K := IsLocalization.lift hu
  have hφ : φ.comp a = (algebraMap B K).comp f := by
    dsimp only [a, φ]
    rw [← RingHom.comp_assoc, IsLocalization.lift_comp]
  have ha : Function.Injective (φ.comp a) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [hφ, ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
    exact (P.over_def (⊥ : Ideal V)).symm
  obtain ⟨W, b, _, _, he⟩ := exists_valuationSubring_factor_of_injective_local_base a φ ha
  refine ⟨CommRingCat.of W, inferInstance, inferInstance, b.comp a,
    b.comp (algebraMap B R), he, ?_⟩
  rfl

end SerrePositivity.AlgebraicGeometry
