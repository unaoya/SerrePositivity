module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import SerrePositivity.CommutativeAlgebra.Perfection
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# 標数 p の完全環の商の perfectoid 化

## 概要
p = 0 の完全環は perfectoid、その任意の商の普遍 perfectoid 化は根基商 R/√J で、全射。
BS 著者版 Corollary 7.3 と Theorem 7.4 の標数 p の場合を、完全環の商で計算する。

## 方針
根基商の完全性を直接示す。

## 規約
今はどこからも使われていない。

## 使われ方
—
-/

universe u

/-! ## pが零である完全環のperfectoid性

N3の標数p商の候補に、既存のIsIntegralPerfectoidの四条件を供給する。
一般strict p環のWitt復元や一般主イデアル商のperfection核は使わない。
-/

@[expose] public noncomputable section CharacteristicPPerfectoid

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- p=0の完全環は、既存の四条件による整perfectoid環である。零環も含む。 -/
theorem Semiperfectoid.isIntegralPerfectoid_of_perfectRing_p_eq_zero [PerfectRing R p]
    (hp : (p : R) = 0) : _root_.SerrePositivity.IsIntegralPerfectoid R p := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact Or.inl hs
  · let := hn
    have hI : Ideal.span {(p : R)} = ⊥ := by simp [hp]
    let : IsAdicComplete (Ideal.span {(p : R)}) R := by rw [hI]; infer_instance
    have hnonunit : ¬ IsUnit (p : R) := by rw [hp]; exact not_isUnit_zero
    let : Fact (¬ IsUnit (p : R)) := ⟨hnonunit⟩
    let E : ModP R p ≃+* R := (Ideal.quotEquivOfEq hI).trans (RingEquiv.quotientBot R)
    let : PerfectRing (ModP R p) p := by
      refine ⟨⟨?_, ?_⟩⟩
      · intro x y hxy
        apply E.injective
        apply (PerfectRing.bijective_frobenius (R := R) (p := p)).1
        simpa only [frobenius_def, ← map_pow] using congrArg E hxy
      · intro x
        obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 (E x)
        refine ⟨E.symm y, ?_⟩
        apply E.injective
        simpa only [frobenius_def, ← map_pow, E.apply_symm_apply] using hy
    let : IsReduced (ModP R p) := _root_.SerrePositivity.isReduced_of_perfectPower (ModP R p) p (Fact.out : p.Prime).one_lt
    have hker : RingHom.ker (WittVector.fontaineTheta R p) =
        Ideal.span {(p : WittVector p (PreTilt R p))} := by
      apply le_antisymm
      · intro w hw
        apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero w).mpr
        apply Perfection.ext
        intro n
        change PreTilt.coeff n (w.coeff 0) = 0
        apply eq_zero_of_pow_eq_zero (n := p ^ n)
        have h0 : PreTilt.coeff 0 (w.coeff 0) = 0 := by
          rw [← WittVector.mk_fontaineTheta, show WittVector.fontaineTheta R p w = 0 from hw]
          exact map_zero _
        simpa only [zero_add, h0] using
          _root_.SerrePositivity.compatibleRoots_pow p (fun m ↦ PreTilt.coeff m (w.coeff 0))
            (fun m ↦ PreTilt.coeff_pow_p _ m) 0 n
      · apply Ideal.span_le.mpr
        rw [Set.singleton_subset_iff]
        change WittVector.fontaineTheta R p (p : WittVector p (PreTilt R p)) = 0
        simpa only [map_natCast] using hp
    refine Or.inr ⟨hnonunit, inferInstance, ⟨0, 1, ?_⟩, ?_, ?_⟩
    · simp [hp, (Fact.out : p.Prime).ne_zero]
    · exact (PerfectRing.bijective_frobenius (R := ModP R p) (p := p)).2
    · rw [hker]
      infer_instance

end SerrePositivity.BhattScholze

end CharacteristicPPerfectoid

/-! ## 完全な標数p環の任意の商のperfectoid化

具体的な根基商R/√Jを使い、存在・IsPerfectoidization普遍性・全射性を分ける。
混標数の一般B3/B4、導来完備化や既存の存在・全射性引用は使用しない。
-/

@[expose] public noncomputable section CharacteristicPQuotient

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [PerfectRing R p]

/-- 完全環の根基商は完全。p=0を明示し、零環も含む。 -/
theorem Semiperfectoid.perfectRing_radical_quotient_of_p_eq_zero (hp : (p : R) = 0) (J : Ideal R) :
    PerfectRing (R ⧸ J.radical) p := by
  rcases subsingleton_or_nontrivial (R ⧸ J.radical) with hs | hn
  · let := hs
    exact ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩⟩
  · let := hn
    have hpQ : (p : R ⧸ J.radical) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J.radical), hp, map_zero]
    let : CharP (R ⧸ J.radical) p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
    let : IsReduced (R ⧸ J.radical) :=
      (Ideal.isRadical_iff_quotient_reduced J.radical).mp (Ideal.radical_isRadical J)
    apply PerfectRing.ofSurjective _ _
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 r
    refine ⟨Ideal.Quotient.mk J.radical s, ?_⟩
    simpa only [frobenius_def, ← map_pow] using congrArg (Ideal.Quotient.mk J.radical) hs

/-- 根基商は既存の四条件を満たすperfectoid環。 -/
theorem Semiperfectoid.radical_quotient_isIntegralPerfectoid_of_p_eq_zero (hp : (p : R) = 0)
    (J : Ideal R) : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ J.radical) p := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectRing_radical_quotient_of_p_eq_zero hp J
  apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.isIntegralPerfectoid_of_perfectRing_p_eq_zero
  rw [← map_natCast (Ideal.Quotient.mk J.radical), hp, map_zero]

/-- 元の商から根基商への具体的な標準射。 -/
def Semiperfectoid.characteristicPQuotientPerfectoidizationMap (J : Ideal R) :
    R ⧸ J →+* R ⧸ J.radical :=
  Ideal.quotientMap _ (RingHom.id R) Ideal.le_radical

/-- 標準射の代表元公式。 -/
@[simp] theorem Semiperfectoid.characteristicPQuotientPerfectoidizationMap_mk (J : Ideal R) (r : R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap J (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk J.radical r := rfl

/-- 標準射の全射性。普遍性の証明とは分ける。 -/
theorem Semiperfectoid.characteristicPQuotientPerfectoidizationMap_surjective (J : Ideal R) :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap J) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- p=0の完全環の任意の商について、根基商への具体的射はperfectoid化である。 -/
theorem Semiperfectoid.characteristicPQuotientPerfectoidizationMap_isPerfectoidization
    (hp : (p : R) = 0) (J : Ideal R) :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap J) := by
  refine ⟨_root_.SerrePositivity.BhattScholze.Semiperfectoid.radical_quotient_isIntegralPerfectoid_of_p_eq_zero hp J, ?_⟩
  intro T _ hT g
  have hpT : (p : T) = 0 := by
    have hpS : (p : R ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), hp, map_zero]
    rw [← map_natCast g, hpS, map_zero]
  let := hT.isReduced_of_p_eq_zero T p hpT
  let f := g.comp (Ideal.Quotient.mk J)
  have hJ : J.radical ≤ RingHom.ker f := by
    intro r hr
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hr
    change f r = 0
    apply eq_zero_of_pow_eq_zero (n := n)
    have hz : f (r ^ n) = 0 := by
      change g (Ideal.Quotient.mk J (r ^ n)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn, map_zero]
    simpa only [map_pow] using hz
  let l := Ideal.Quotient.lift J.radical f hJ
  have hl : l.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap J) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply RingHom.ext
  intro x
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap_surjective J x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hl s).symm

/-- p=0の完全環の任意の商には、環として普遍なperfectoid化が存在する。
全射性は別の公開定理とし、この存在命題には含めない。 -/
theorem Semiperfectoid.exists_perfectoidization_of_perfect_p_eq_zero_quotient
    (hp : (p : R) = 0) (J : Ideal R) :
    ∃ (C : Type u) (_ : CommRing C) (f : R ⧸ J →+* C), _root_.SerrePositivity.IsPerfectoidization p f :=
  ⟨R ⧸ J.radical, inferInstance, _root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap J,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.characteristicPQuotientPerfectoidizationMap_isPerfectoidization hp J⟩

end SerrePositivity.BhattScholze

end CharacteristicPQuotient
