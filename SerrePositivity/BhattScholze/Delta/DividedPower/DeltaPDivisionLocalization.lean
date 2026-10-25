module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaPTorsionReduction

/-! # p除算添加環のp局所化

任意元族について、A{a_s/p}[1/p]をA[1/p]と具体的δ環同型で比較する。
正則性・有限性・完備性は要求しない。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (a : σ → A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a
local notation "Aₚ" => Localization.Away (p : A)
local notation "Bₚ" => Localization.Away (p : B₀)

/-- p冪局所化上の既存δ構造の具体的特殊化。 -/
abbrev deltaPDivisionAwayStructure : DeltaStructure p Aₚ :=
  D.localization (Submonoid.powers (p : A)) Aₚ D.powers_p_frobenius_stable

/-- 元の環からp局所化への標準射はδ射。 -/
theorem deltaPDivisionAwayStructure_base_isDeltaHom :
    D.IsDeltaHom (deltaPDivisionAwayStructure D) (algebraMap A Aₚ) :=
  D.isDeltaHom_localization (Submonoid.powers (p : A)) Aₚ D.powers_p_frobenius_stable

/-- 各除算変数をa_s/pへ送るδ射が一意に存在する。 -/
theorem existsUnique_deltaPDivisionToAway :
    ∃! f : B₀ →+* Aₚ, (E₀).IsDeltaHom (deltaPDivisionAwayStructure D) f ∧
      f.comp j₀ = algebraMap A Aₚ ∧ ∀ s,
        f (deltaAdjoinDivisionVariable D (p : A) a s) =
          IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s) := by
  apply existsUnique_deltaAdjoinDivisionHom D (deltaPDivisionAwayStructure D) (p : A) a
    (algebraMap A Aₚ) (deltaPDivisionAwayStructure_base_isDeltaHom D)
    (fun s ↦ IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s))
  intro s
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]

/-- raw p除算添加環からA[1/p]への具体的δ射。 -/
def deltaPDivisionToAway : B₀ →+* Aₚ := (existsUnique_deltaPDivisionToAway D a).choose

/-- 具体的δ射のδ・基底・除算変数上の式。 -/
theorem deltaPDivisionToAway_spec :
    (E₀).IsDeltaHom (deltaPDivisionAwayStructure D) (deltaPDivisionToAway D a) ∧
      (deltaPDivisionToAway D a).comp j₀ = algebraMap A Aₚ ∧ ∀ s,
        deltaPDivisionToAway D a (deltaAdjoinDivisionVariable D (p : A) a s) =
          IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s) :=
  (existsUnique_deltaPDivisionToAway D a).choose_spec.1

omit [Fact p.Prime] in
private theorem map_powers_isUnit {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (h : IsUnit (f (p : R))) (s : Submonoid.powers (p : R)) : IsUnit (f s) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) (p : R)).mp s.property
  rw [← hn, map_pow]
  exact h.pow n

/-- A[1/p]からp除算添加環のp局所化へのδ延長が一意に存在する。 -/
theorem existsUnique_deltaPDivisionAwayToAway :
    ∃! f : Aₚ →+* Bₚ,
      f.comp (algebraMap A Aₚ) = (algebraMap B₀ Bₚ).comp j₀ ∧
        (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀) f := by
  apply D.existsUnique_localization_lift (Submonoid.powers (p : A)) Aₚ
    D.powers_p_frobenius_stable (deltaPDivisionAwayStructure E₀)
    ((algebraMap B₀ Bₚ).comp j₀)
    ((deltaPDivisionAwayStructure_base_isDeltaHom E₀).comp
      (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a))
  apply map_powers_isUnit
  have hp := IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B₀)
  have he : ((algebraMap B₀ Bₚ).comp j₀) (p : A) = algebraMap B₀ Bₚ (p : B₀) :=
    congrArg (algebraMap B₀ Bₚ) (map_natCast j₀ p)
  exact he.symm ▸ hp

/-- 局所化間の正方向の具体的δ射。 -/
def deltaPDivisionAwayToAway : Aₚ →+* Bₚ :=
  (existsUnique_deltaPDivisionAwayToAway D a).choose

/-- 正方向の局所化射は標準基底射とδ構造を保つ。 -/
theorem deltaPDivisionAwayToAway_spec :
    (deltaPDivisionAwayToAway D a).comp (algebraMap A Aₚ) = (algebraMap B₀ Bₚ).comp j₀ ∧
      (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀)
        (deltaPDivisionAwayToAway D a) :=
  (existsUnique_deltaPDivisionAwayToAway D a).choose_spec.1

/-- rawδ射はp除算添加環のp局所化から一意に延長する。 -/
theorem existsUnique_deltaPDivisionAwayFromAway :
    ∃! f : Bₚ →+* Aₚ,
      f.comp (algebraMap B₀ Bₚ) = deltaPDivisionToAway D a ∧
        (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D) f := by
  apply (E₀).existsUnique_localization_lift (Submonoid.powers (p : B₀)) Bₚ
    (E₀).powers_p_frobenius_stable (deltaPDivisionAwayStructure D)
    (deltaPDivisionToAway D a) (deltaPDivisionToAway_spec D a).1
  apply map_powers_isUnit
  have hp := IsLocalization.Away.algebraMap_isUnit (S := Aₚ) (p : A)
  have he : deltaPDivisionToAway D a (p : B₀) = algebraMap A Aₚ (p : A) :=
    (map_natCast (deltaPDivisionToAway D a) p).trans (map_natCast (algebraMap A Aₚ) p).symm
  exact he.symm ▸ hp

/-- 局所化間の逆方向の具体的δ射。 -/
def deltaPDivisionAwayFromAway : Bₚ →+* Aₚ :=
  (existsUnique_deltaPDivisionAwayFromAway D a).choose

/-- 逆方向の局所化射も標準単位とδ構造を保つ。 -/
theorem deltaPDivisionAwayFromAway_spec :
    (deltaPDivisionAwayFromAway D a).comp (algebraMap B₀ Bₚ) = deltaPDivisionToAway D a ∧
      (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D)
        (deltaPDivisionAwayFromAway D a) :=
  (existsUnique_deltaPDivisionAwayFromAway D a).choose_spec.1

/-- rawδ包上では、正方向と具体的δ評価の合成は標準p局所化射。 -/
theorem deltaPDivisionAwayToAway_comp_toAway :
    (deltaPDivisionAwayToAway D a).comp (deltaPDivisionToAway D a) = algebraMap B₀ Bₚ := by
  let g := (algebraMap B₀ Bₚ).comp j₀
  have hg : D.IsDeltaHom (deltaPDivisionAwayStructure E₀) g :=
    (deltaPDivisionAwayStructure_base_isDeltaHom E₀).comp
      (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a)
  have hp : IsUnit (g (p : A)) := by
    have he : g (p : A) = algebraMap B₀ Bₚ (p : B₀) :=
      congrArg (algebraMap B₀ Bₚ) (map_natCast j₀ p)
    exact he.symm ▸ IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B₀)
  obtain ⟨u, hu⟩ := hp
  have ha : ∀ s, g (p : A) ∣ g (a s) := by
    intro s
    refine ⟨(u⁻¹ : Bₚˣ) * g (a s), ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨f, _, hf⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D
    (deltaPDivisionAwayStructure E₀) (p : A) a g hg
    (fun _ _ h ↦ (show IsUnit (g (p : A)) from hu ▸ u.isUnit).mul_left_cancel h) ha
  have h₁ : ((deltaPDivisionAwayToAway D a).comp (deltaPDivisionToAway D a)).comp j₀ = g := by
    rw [RingHom.comp_assoc, (deltaPDivisionToAway_spec D a).2.1,
      (deltaPDivisionAwayToAway_spec D a).1]
  exact (hf _ ⟨(deltaPDivisionAwayToAway_spec D a).2.comp (deltaPDivisionToAway_spec D a).1,
    h₁⟩).trans (hf _ ⟨deltaPDivisionAwayStructure_base_isDeltaHom E₀, rfl⟩).symm

/-- 正逆方向の局所化射の合成はA[1/p]の恒等射。 -/
theorem deltaPDivisionAwayFromAway_comp_toAway :
    (deltaPDivisionAwayFromAway D a).comp (deltaPDivisionAwayToAway D a) = RingHom.id Aₚ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
  rw [RingHom.comp_assoc, (deltaPDivisionAwayToAway_spec D a).1, ← RingHom.comp_assoc,
    (deltaPDivisionAwayFromAway_spec D a).1, (deltaPDivisionToAway_spec D a).2.1,
    RingHom.id_comp]

/-- 逆順の局所化射の合成も恒等射。 -/
theorem deltaPDivisionAwayToAway_comp_fromAway :
    (deltaPDivisionAwayToAway D a).comp (deltaPDivisionAwayFromAway D a) = RingHom.id Bₚ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : B₀))
  rw [RingHom.comp_assoc, (deltaPDivisionAwayFromAway_spec D a).1,
    deltaPDivisionAwayToAway_comp_toAway, RingHom.id_comp]

/-- 一般元族のraw p除算添加環のp局所化はA[1/p]と具体的に同型。 -/
def deltaPDivisionLocalizationEquiv : Aₚ ≃+* Bₚ :=
  RingEquiv.ofRingHom (deltaPDivisionAwayToAway D a) (deltaPDivisionAwayFromAway D a)
    (deltaPDivisionAwayToAway_comp_fromAway D a) (deltaPDivisionAwayFromAway_comp_toAway D a)

/-- 局所化比較同型の両方向はδ構造と両立する。 -/
theorem deltaPDivisionLocalizationEquiv_isDeltaHom :
    (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀)
        (deltaPDivisionLocalizationEquiv D a).toRingHom ∧
      (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D)
        (deltaPDivisionLocalizationEquiv D a).symm.toRingHom :=
  ⟨(deltaPDivisionAwayToAway_spec D a).2, (deltaPDivisionAwayFromAway_spec D a).2⟩

/-- 局所化比較同型は元のAからの標準射を保つ。 -/
theorem deltaPDivisionLocalizationEquiv_comp_base :
    (deltaPDivisionLocalizationEquiv D a).toRingHom.comp (algebraMap A Aₚ) =
      (algebraMap B₀ Bₚ).comp j₀ := (deltaPDivisionAwayToAway_spec D a).1

/-- 逆比較同型はrawδ包からの標準射を具体的δ評価へ送る。 -/
theorem deltaPDivisionLocalizationEquiv_symm_comp_base :
    (deltaPDivisionLocalizationEquiv D a).symm.toRingHom.comp (algebraMap B₀ Bₚ) =
      deltaPDivisionToAway D a := (deltaPDivisionAwayFromAway_spec D a).1

end SerrePositivity.BhattScholze
