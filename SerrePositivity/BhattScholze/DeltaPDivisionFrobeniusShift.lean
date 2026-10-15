module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionSum

/-! # φ(y)/pとy^p/pのδ除算添加環の座標変換

φ(y)=y^p+pδ(y)に従って初期除算変数を平行移動する。
完備化・分冪構造・平坦性はこの代数的同型の結論に含めない。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A)
local notation "Bφ" => DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "Bpow" => DeltaAdjoinDivision D (p : A) (fun s ↦ y s ^ p)
local notation "Dφ" => deltaAdjoinDivisionStructure D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "Dpow" => deltaAdjoinDivisionStructure D (p : A) (fun s ↦ y s ^ p)
local notation "jφ" => deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "jpow" => deltaAdjoinDivisionMap D (p : A) (fun s ↦ y s ^ p)
local notation "vφ" => deltaAdjoinDivisionVariable D (p : A) (fun s ↦ D.frobeniusLift (y s))
local notation "vpow" => deltaAdjoinDivisionVariable D (p : A) (fun s ↦ y s ^ p)

/-- 正方向の平行移動を指定するδ射は一意に存在する。 -/
theorem existsUnique_deltaPDivisionFrobeniusToPower :
    ∃! f : Bφ →+* Bpow, (Dφ).IsDeltaHom Dpow f ∧ f.comp jφ = jpow ∧
      ∀ s, f (vφ s) = vpow s + jpow (D.delta (y s)) := by
  apply existsUnique_deltaAdjoinDivisionHom D Dpow (p : A)
    (fun s ↦ D.frobeniusLift (y s)) jpow
    (deltaAdjoinDivisionMap_isDeltaHom D (p : A) (fun s ↦ y s ^ p))
    (fun s ↦ vpow s + jpow (D.delta (y s)))
  intro s
  calc
    jpow (p : A) * (vpow s + jpow (D.delta (y s))) =
        jpow (y s ^ p) + jpow ((p : A) * D.delta (y s)) := by
      rw [mul_add, deltaAdjoinDivision_relation, map_mul]
    _ = jpow (D.frobeniusLift (y s)) := by rw [← map_add, D.frobeniusLift_apply]

/-- φ(y)/pをy^p/p+δ(y)へ送る具体的δ射。 -/
def deltaPDivisionFrobeniusToPower : Bφ →+* Bpow :=
  (existsUnique_deltaPDivisionFrobeniusToPower D y).choose

/-- 正方向の射はδ・基底射・初期除算変数と両立する。 -/
theorem deltaPDivisionFrobeniusToPower_spec :
    (Dφ).IsDeltaHom Dpow (deltaPDivisionFrobeniusToPower D y) ∧
      (deltaPDivisionFrobeniusToPower D y).comp jφ = jpow ∧
      ∀ s, deltaPDivisionFrobeniusToPower D y (vφ s) = vpow s + jpow (D.delta (y s)) :=
  (existsUnique_deltaPDivisionFrobeniusToPower D y).choose_spec.1

/-- 逆方向の平行移動を指定するδ射も一意に存在する。 -/
theorem existsUnique_deltaPDivisionPowerToFrobenius :
    ∃! f : Bpow →+* Bφ, (Dpow).IsDeltaHom Dφ f ∧ f.comp jpow = jφ ∧
      ∀ s, f (vpow s) = vφ s - jφ (D.delta (y s)) := by
  apply existsUnique_deltaAdjoinDivisionHom D Dφ (p : A) (fun s ↦ y s ^ p) jφ
    (deltaAdjoinDivisionMap_isDeltaHom D (p : A) (fun s ↦ D.frobeniusLift (y s)))
    (fun s ↦ vφ s - jφ (D.delta (y s)))
  intro s
  calc
    jφ (p : A) * (vφ s - jφ (D.delta (y s))) =
        jφ (D.frobeniusLift (y s)) - jφ ((p : A) * D.delta (y s)) := by
      rw [mul_sub, deltaAdjoinDivision_relation, map_mul]
    _ = jφ (y s ^ p) := by rw [D.frobeniusLift_apply, map_add]; ring

/-- y^p/pをφ(y)/p−δ(y)へ送る逆方向の具体的δ射。 -/
def deltaPDivisionPowerToFrobenius : Bpow →+* Bφ :=
  (existsUnique_deltaPDivisionPowerToFrobenius D y).choose

/-- 逆方向の射もδ・基底射・初期除算変数と両立する。 -/
theorem deltaPDivisionPowerToFrobenius_spec :
    (Dpow).IsDeltaHom Dφ (deltaPDivisionPowerToFrobenius D y) ∧
      (deltaPDivisionPowerToFrobenius D y).comp jpow = jφ ∧
      ∀ s, deltaPDivisionPowerToFrobenius D y (vpow s) = vφ s - jφ (D.delta (y s)) :=
  (existsUnique_deltaPDivisionPowerToFrobenius D y).choose_spec.1

/-- 除算変数の正負の平行移動を続けると元に戻る。 -/
theorem deltaPDivisionPowerToFrobenius_comp_toPower :
    (deltaPDivisionPowerToFrobenius D y).comp (deltaPDivisionFrobeniusToPower D y) =
      RingHom.id Bφ := by
  have h₁ := deltaPDivisionFrobeniusToPower_spec D y
  have h₂ := deltaPDivisionPowerToFrobenius_spec D y
  apply deltaAdjoinDivisionHom_ext D Dφ (p : A) (fun s ↦ D.frobeniusLift (y s))
    _ _ (h₂.1.comp h₁.1) (Dφ).isDeltaHom_id
  · rw [RingHom.comp_assoc, h₁.2.1, h₂.2.1, RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, h₁.2.2, map_add, h₂.2.2]
    have hb := DFunLike.congr_fun h₂.2.1 (D.delta (y s))
    change deltaPDivisionPowerToFrobenius D y (jpow (D.delta (y s))) = _ at hb
    rw [hb, sub_add_cancel]
    rfl

/-- 逆順の平行移動も恒等射を与える。 -/
theorem deltaPDivisionFrobeniusToPower_comp_toFrobenius :
    (deltaPDivisionFrobeniusToPower D y).comp (deltaPDivisionPowerToFrobenius D y) =
      RingHom.id Bpow := by
  have h₁ := deltaPDivisionFrobeniusToPower_spec D y
  have h₂ := deltaPDivisionPowerToFrobenius_spec D y
  apply deltaAdjoinDivisionHom_ext D Dpow (p : A) (fun s ↦ y s ^ p)
    _ _ (h₁.1.comp h₂.1) (Dpow).isDeltaHom_id
  · rw [RingHom.comp_assoc, h₂.2.1, h₁.2.1, RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, h₂.2.2, map_sub, h₁.2.2]
    have hb := DFunLike.congr_fun h₁.2.1 (D.delta (y s))
    change deltaPDivisionFrobeniusToPower D y (jφ (D.delta (y s))) = _ at hb
    rw [hb, add_sub_cancel_right]
    rfl

/-- φ(y_s)/pとy_s^p/pのrawδ添加環の具体的な環同型。 -/
def deltaPDivisionFrobeniusShiftEquiv : Bφ ≃+* Bpow :=
  RingEquiv.ofRingHom (deltaPDivisionFrobeniusToPower D y) (deltaPDivisionPowerToFrobenius D y)
    (deltaPDivisionFrobeniusToPower_comp_toFrobenius D y)
    (deltaPDivisionPowerToFrobenius_comp_toPower D y)

/-- 同型の両方向は実際のδ構造と可換。 -/
theorem deltaPDivisionFrobeniusShiftEquiv_isDeltaHom :
    (Dφ).IsDeltaHom Dpow (deltaPDivisionFrobeniusShiftEquiv D y).toRingHom ∧
      (Dpow).IsDeltaHom Dφ (deltaPDivisionFrobeniusShiftEquiv D y).symm.toRingHom :=
  ⟨(deltaPDivisionFrobeniusToPower_spec D y).1, (deltaPDivisionPowerToFrobenius_spec D y).1⟩

/-- 同型は元の基底環からの標準射を保つ。 -/
theorem deltaPDivisionFrobeniusShiftEquiv_comp :
    (deltaPDivisionFrobeniusShiftEquiv D y).toRingHom.comp jφ = jpow :=
  (deltaPDivisionFrobeniusToPower_spec D y).2.1

/-- 同型の初期除算変数上の正方向の式。 -/
theorem deltaPDivisionFrobeniusShiftEquiv_variable (s : σ) :
    deltaPDivisionFrobeniusShiftEquiv D y (vφ s) = vpow s + jpow (D.delta (y s)) :=
  (deltaPDivisionFrobeniusToPower_spec D y).2.2 s

/-- 同型の初期除算変数上の逆方向の式。 -/
theorem deltaPDivisionFrobeniusShiftEquiv_symm_variable (s : σ) :
    (deltaPDivisionFrobeniusShiftEquiv D y).symm (vpow s) = vφ s - jφ (D.delta (y s)) :=
  (deltaPDivisionPowerToFrobenius_spec D y).2.2 s

end SerrePositivity.BhattScholze
