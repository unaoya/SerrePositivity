module

public import SerrePositivity.BhattScholze.DeltaQuotient
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Regular.Basic

/-! # d冪ねじれのδ閉包による商

BS著者公開版Proposition 7.2のB/B[d^∞]_δの代数的部分。
通常のd冪ねじれはMathlibの局所化射の核として扱い、新しいねじれイデアルを重複定義しない。
商の新しいdねじれの不存在や導来完備化はここでは結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- dの冪で消える元は、局所化射の核のδ閉包に属する。
Prop 7.2で旧d冪ねじれを商で消す際の具体的な包含。 -/
theorem pow_torsion_mem_deltaClosure_ker_away (D : DeltaStructure p R) (d : R)
    (N : ℕ) (x : R) (hx : d ^ N * x = 0) :
    x ∈ D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))) := by
  apply D.le_deltaClosure
  change algebraMap R (Localization.Away d) x = 0
  apply (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) x).mpr
  exact ⟨⟨d ^ N, (Submonoid.mem_powers_iff (d ^ N) d).mpr ⟨N, rfl⟩⟩, hx⟩

/-- δ射fの終域でf(d)が非零因子なら、d冪ねじれのδ閉包をfは零に送る。
局所化の核の判定、正則元の冪の消去、δ閉包の最小性を再利用する。 -/
theorem IsDeltaHom.deltaClosure_ker_away_le_ker {A : Type v} [CommRing A]
    {D : DeltaStructure p R} {E : DeltaStructure p A} {f : R →+* A}
    (hf : D.IsDeltaHom E f) (d : R)
    (hd : Function.Injective (fun x : A ↦ f d * x)) :
    D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))) ≤ RingHom.ker f := by
  apply hf.deltaClosure_le_ker
  intro x hx
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) x).mp hx
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : R) d).mp m.property
  have h := congrArg f hm
  rw [← hN, map_mul, map_pow, map_zero] at h
  have hreg : IsLeftRegular (f d) := hd
  exact (IsLeftRegular.pow N hreg) (h.trans (mul_zero _).symm)

/-- δ射fがdを非零因子へ送るなら、d冪ねじれのδ閉包商から一意なδ射に降下する。
環・標準商写像・δ構造を明示したProp 7.2のねじれ除去段階の普遍性。 -/
theorem existsUnique_torsionReductionHom (D : DeltaStructure p R) (d : R)
    {A : Type v} [CommRing A] (E : DeltaStructure p A) (f : R →+* A)
    (hf : D.IsDeltaHom E f) (hd : Function.Injective (fun x : A ↦ f d * x)) :
    ∃! g : (R ⧸ D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d)))) →+* A,
      g.comp (Ideal.Quotient.mk
        (D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))))) = f ∧
      (D.quotient (D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))))
        (D.isStable_deltaClosure _)).IsDeltaHom E g :=
  D.existsUnique_quotient_lift _ (D.isStable_deltaClosure _) E f hf
    (hf.deltaClosure_ker_away_le_ker d hd)

end SerrePositivity.BhattScholze.DeltaStructure
