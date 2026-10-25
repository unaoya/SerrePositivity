module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShift
public import SerrePositivity.BhattScholze.Delta.Division.DeltaPTorsionReduction
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionClassicalCompletion
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionQuotient

/-! # φ(y)/pとy^p/pの旧pねじれ除去商の比較

既存のp正則性とδ商普遍性によりraw平行移動を移す。
完備化後の平坦性・分冪構造はこの結果には含めない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A)
local notation "Qφ" => DeltaDivisionTorsionQuotient D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "Qpow" => DeltaDivisionTorsionQuotient D (p : A) (fun s ↦ y s ^ p)
local notation "Eφ" => deltaDivisionTorsionStructure D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "Epow" => deltaDivisionTorsionStructure D (p : A) (fun s ↦ y s ^ p)
local notation "jφ" => deltaDivisionTorsionMap D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "jpow" => deltaDivisionTorsionMap D (p : A) (fun s ↦ y s ^ p)

private theorem exists_torsionMap_of_raw (a b : σ → A)
    (F : DeltaAdjoinDivision D (p : A) a →+* DeltaAdjoinDivision D (p : A) b)
    (hbase : F.comp (deltaAdjoinDivisionMap D (p : A) a) =
      deltaAdjoinDivisionMap D (p : A) b) :
    ∃! f : DeltaDivisionTorsionQuotient D (p : A) a →+*
        DeltaDivisionTorsionQuotient D (p : A) b,
      (deltaDivisionTorsionStructure D (p : A) a).IsDeltaHom
          (deltaDivisionTorsionStructure D (p : A) b) f ∧
        f.comp (deltaDivisionTorsionMap D (p : A) a) = deltaDivisionTorsionMap D (p : A) b := by
  let q : DeltaAdjoinDivision D (p : A) b →+* DeltaDivisionTorsionQuotient D (p : A) b :=
    Ideal.Quotient.mk _
  let k := q.comp F
  have hk : k.comp (deltaAdjoinDivisionMap D (p : A) a) =
      deltaDivisionTorsionMap D (p : A) b := by
    change (q.comp F).comp _ = q.comp _
    rw [RingHom.comp_assoc, hbase]
  apply existsUnique_deltaDivisionTorsionHom D
    (deltaDivisionTorsionStructure D (p : A) b) (p : A) a
    (deltaDivisionTorsionMap D (p : A) b) (deltaDivisionTorsionMap_isDeltaHom D (p : A) b)
  · simpa only [map_natCast (deltaDivisionTorsionMap D (p : A) b) p] using
      deltaDivisionTorsionQuotient_p_mul_injective D b
  · intro s
    exact ⟨k (deltaAdjoinDivisionVariable D (p : A) a s),
      (deltaAdjoinDivisionHom_relation D (p : A) a
        (deltaDivisionTorsionMap D (p : A) b) k hk s).symm⟩

/-- 正方向のraw平行移動は既存の旧pねじれ除去商間へ一意に降りる。 -/
theorem existsUnique_deltaPDivisionTorsionFrobeniusToPower :
    ∃! f : Qφ →+* Qpow, (Eφ).IsDeltaHom Epow f ∧ f.comp jφ = jpow :=
  exists_torsionMap_of_raw D _ _ (deltaPDivisionFrobeniusToPower D y)
    (deltaPDivisionFrobeniusToPower_spec D y).2.1

/-- 正方向の旧ねじれ除去商間の具体的標準射。 -/
def deltaPDivisionTorsionFrobeniusToPower : Qφ →+* Qpow :=
  (existsUnique_deltaPDivisionTorsionFrobeniusToPower D y).choose

/-- 正方向の商射はδ構造と標準基底射を保つ。 -/
theorem deltaPDivisionTorsionFrobeniusToPower_spec :
    (Eφ).IsDeltaHom Epow (deltaPDivisionTorsionFrobeniusToPower D y) ∧
      (deltaPDivisionTorsionFrobeniusToPower D y).comp jφ = jpow :=
  (existsUnique_deltaPDivisionTorsionFrobeniusToPower D y).choose_spec.1

/-- 逆方向のraw平行移動も既存の旧pねじれ除去商間へ一意に降りる。 -/
theorem existsUnique_deltaPDivisionTorsionPowerToFrobenius :
    ∃! f : Qpow →+* Qφ, (Epow).IsDeltaHom Eφ f ∧ f.comp jpow = jφ :=
  exists_torsionMap_of_raw D _ _ (deltaPDivisionPowerToFrobenius D y)
    (deltaPDivisionPowerToFrobenius_spec D y).2.1

/-- 逆方向の旧ねじれ除去商間の具体的標準射。 -/
def deltaPDivisionTorsionPowerToFrobenius : Qpow →+* Qφ :=
  (existsUnique_deltaPDivisionTorsionPowerToFrobenius D y).choose

/-- 逆方向の商射もδ構造と標準基底射を保つ。 -/
theorem deltaPDivisionTorsionPowerToFrobenius_spec :
    (Epow).IsDeltaHom Eφ (deltaPDivisionTorsionPowerToFrobenius D y) ∧
      (deltaPDivisionTorsionPowerToFrobenius D y).comp jpow = jφ :=
  (existsUnique_deltaPDivisionTorsionPowerToFrobenius D y).choose_spec.1

private theorem torsionEndomorphism_eq_id (a : σ → A)
    (f : DeltaDivisionTorsionQuotient D (p : A) a →+* DeltaDivisionTorsionQuotient D (p : A) a)
    (hf : (deltaDivisionTorsionStructure D (p : A) a).IsDeltaHom
      (deltaDivisionTorsionStructure D (p : A) a) f)
    (hb : f.comp (deltaDivisionTorsionMap D (p : A) a) = deltaDivisionTorsionMap D (p : A) a) :
    f = RingHom.id _ := by
  obtain ⟨k, _, hu⟩ := existsUnique_deltaDivisionTorsionHom D
    (deltaDivisionTorsionStructure D (p : A) a) (p : A) a
    (deltaDivisionTorsionMap D (p : A) a) (deltaDivisionTorsionMap_isDeltaHom D (p : A) a)
    (by simpa only [map_natCast (deltaDivisionTorsionMap D (p : A) a) p] using
      deltaDivisionTorsionQuotient_p_mul_injective D a)
    (deltaDivisionTorsionMap_dvd D (p : A) a)
  exact (hu f ⟨hf, hb⟩).trans
    (hu (RingHom.id _) ⟨(deltaDivisionTorsionStructure D (p : A) a).isDeltaHom_id,
      RingHom.id_comp _⟩).symm

/-- 旧ねじれ除去商の正逆方向の合成は恒等射。 -/
theorem deltaPDivisionTorsionPowerToFrobenius_comp_toPower :
    (deltaPDivisionTorsionPowerToFrobenius D y).comp
      (deltaPDivisionTorsionFrobeniusToPower D y) = RingHom.id Qφ := by
  have h₁ := deltaPDivisionTorsionFrobeniusToPower_spec D y
  have h₂ := deltaPDivisionTorsionPowerToFrobenius_spec D y
  apply torsionEndomorphism_eq_id D _ _ (h₂.1.comp h₁.1)
  rw [RingHom.comp_assoc, h₁.2, h₂.2]

/-- 旧ねじれ除去商の逆順の合成も恒等射。 -/
theorem deltaPDivisionTorsionFrobeniusToPower_comp_toFrobenius :
    (deltaPDivisionTorsionFrobeniusToPower D y).comp
      (deltaPDivisionTorsionPowerToFrobenius D y) = RingHom.id Qpow := by
  have h₁ := deltaPDivisionTorsionFrobeniusToPower_spec D y
  have h₂ := deltaPDivisionTorsionPowerToFrobenius_spec D y
  apply torsionEndomorphism_eq_id D _ _ (h₁.1.comp h₂.1)
  rw [RingHom.comp_assoc, h₂.2, h₁.2]

/-- φ(y)/pとy^p/pの既存旧pねじれ除去商を結ぶ具体的同型。 -/
def deltaPDivisionFrobeniusShiftTorsionEquiv : Qφ ≃+* Qpow :=
  RingEquiv.ofRingHom (deltaPDivisionTorsionFrobeniusToPower D y)
    (deltaPDivisionTorsionPowerToFrobenius D y)
    (deltaPDivisionTorsionFrobeniusToPower_comp_toFrobenius D y)
    (deltaPDivisionTorsionPowerToFrobenius_comp_toPower D y)

/-- 同型の両方向は既存の商δ構造と両立する。 -/
theorem deltaPDivisionFrobeniusShiftTorsionEquiv_isDeltaHom :
    (Eφ).IsDeltaHom Epow (deltaPDivisionFrobeniusShiftTorsionEquiv D y).toRingHom ∧
      (Epow).IsDeltaHom Eφ (deltaPDivisionFrobeniusShiftTorsionEquiv D y).symm.toRingHom :=
  ⟨(deltaPDivisionTorsionFrobeniusToPower_spec D y).1,
    (deltaPDivisionTorsionPowerToFrobenius_spec D y).1⟩

/-- 旧ねじれ除去商の同型も元の基底射を保つ。 -/
theorem deltaPDivisionFrobeniusShiftTorsionEquiv_comp :
    (deltaPDivisionFrobeniusShiftTorsionEquiv D y).toRingHom.comp jφ = jpow :=
  (deltaPDivisionTorsionFrobeniusToPower_spec D y).2

end SerrePositivity.BhattScholze
