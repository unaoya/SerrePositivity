module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.CharacteristicPPerfectoid
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # 完全な標数p環の任意の商のperfectoid化

具体的な根基商R/√Jを使い、存在・IsPerfectoidization普遍性・全射性を分ける。
混標数の一般B3/B4、導来完備化や既存の存在・全射性引用は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [PerfectRing R p]

/-- 完全環の根基商は完全。p=0を明示し、零環も含む。 -/
theorem perfectRing_radical_quotient_of_p_eq_zero (hp : (p : R) = 0) (J : Ideal R) :
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
theorem radical_quotient_isIntegralPerfectoid_of_p_eq_zero (hp : (p : R) = 0)
    (J : Ideal R) : IsIntegralPerfectoid (R ⧸ J.radical) p := by
  let := perfectRing_radical_quotient_of_p_eq_zero hp J
  apply isIntegralPerfectoid_of_perfectRing_p_eq_zero
  rw [← map_natCast (Ideal.Quotient.mk J.radical), hp, map_zero]

/-- 元の商から根基商への具体的な標準射。 -/
def characteristicPQuotientPerfectoidizationMap (J : Ideal R) :
    R ⧸ J →+* R ⧸ J.radical :=
  Ideal.quotientMap _ (RingHom.id R) Ideal.le_radical

/-- 標準射の代表元公式。 -/
@[simp] theorem characteristicPQuotientPerfectoidizationMap_mk (J : Ideal R) (r : R) :
    characteristicPQuotientPerfectoidizationMap J (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk J.radical r := rfl

/-- 標準射の全射性。普遍性の証明とは分ける。 -/
theorem characteristicPQuotientPerfectoidizationMap_surjective (J : Ideal R) :
    Function.Surjective (characteristicPQuotientPerfectoidizationMap J) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- p=0の完全環の任意の商について、根基商への具体的射はperfectoid化である。 -/
theorem characteristicPQuotientPerfectoidizationMap_isPerfectoidization
    (hp : (p : R) = 0) (J : Ideal R) :
    IsPerfectoidization p (characteristicPQuotientPerfectoidizationMap J) := by
  refine ⟨radical_quotient_isIntegralPerfectoid_of_p_eq_zero hp J, ?_⟩
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
  have hl : l.comp (characteristicPQuotientPerfectoidizationMap J) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply RingHom.ext
  intro x
  obtain ⟨s, rfl⟩ := characteristicPQuotientPerfectoidizationMap_surjective J x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hl s).symm

/-- p=0の完全環の任意の商には、環として普遍なperfectoid化が存在する。
全射性は別の公開定理とし、この存在命題には含めない。 -/
theorem exists_perfectoidization_of_perfect_p_eq_zero_quotient
    (hp : (p : R) = 0) (J : Ideal R) :
    ∃ (C : Type u) (_ : CommRing C) (f : R ⧸ J →+* C), IsPerfectoidization p f :=
  ⟨R ⧸ J.radical, inferInstance, characteristicPQuotientPerfectoidizationMap J,
    characteristicPQuotientPerfectoidizationMap_isPerfectoidization hp J⟩

end SerrePositivity.BhattScholze
