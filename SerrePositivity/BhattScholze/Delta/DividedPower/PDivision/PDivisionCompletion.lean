module

public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra

/-!
# 生の A{a/p} とその完備化（BS 著者版 Corollary 2.39 の導来側・BS 著者版 Proposition 3.13 の部品）

## 概要
φ(y)/p と y^p/p の δ 除算添加環の座標変換（Frobenius 平行移動）と、その p ねじれ除去商・導来完備化 H⁰ での比較、distinguished 元 a = p·u の単元係数（古典的・導来の p 除算候補）。

## 方針
生の包の p 完備化を構成する。BS 著者版 Corollary 2.44・Proposition 3.13 の対象を作るための部品。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`。
-/

universe u v w

/-! ## φ(y)/pとy^p/pのδ除算添加環の座標変換

φ(y)=y^p+pδ(y)に従って初期除算変数を平行移動する。
完備化・分冪構造・平坦性はこの代数的同型の結論に含めない。
-/

@[expose] public noncomputable section DeltaPDivisionFrobeniusShift

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

end DeltaPDivisionFrobeniusShift

/-! ## 実導来p除算候補の具体的な単元係数

既存の実H⁰候補にG6を適用する。古典的完備化への置換は行わない。
-/

@[expose] public noncomputable section DeltaPDivisionDerivedUnit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
attribute [local instance] derivedDeltaDivisionCommRing
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a
local notation "j₀" => deltaDivisionTorsionMap D (p : A) a

/-- 除算変数の既存実導来完備化H⁰への標準像。 -/
def derivedPDivisionVariable (s : σ) : C₀ :=
  pdCompletionUnit U₀ p ((j₀) (p : A))
    (Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D (p : A) a s))

/-- 実候補内の標準除算変数はp*u_s=j(a_s)を満たす。 -/
theorem derivedPDivisionVariable_relation (s : σ) :
    (p : C₀) * derivedPDivisionVariable D a s =
      derivedDeltaDivisionMap D (p : A) a (a s) := by
  let q : DeltaAdjoinDivision D (p : A) a →+* U₀ := Ideal.Quotient.mk _
  let k := (pdCompletionUnit U₀ p ((j₀) (p : A))).comp q
  have h := congrArg k (deltaAdjoinDivision_relation D (p : A) a s)
  rw [map_mul] at h
  have hk : k (deltaAdjoinDivisionMap D (p : A) a (p : A)) = (p : C₀) := by
    simp only [map_natCast]
  rw [hk] at h
  exact h

/-- G6により、実導来p除算候補内のpはJacobson根基に属する。 -/
theorem derivedPDivision_p_mem_jacobson : (p : C₀) ∈ Ideal.jacobson (⊥ : Ideal C₀) :=
  mem_jacobson_bot_of_isModuleComplete C₀ (p : C₀)
    (derivedDeltaDivision_complete_p D (p : A) a)

/-- distinguished入力の標準除算変数像は実導来候補内でも単元。 -/
theorem derivedPDivisionVariable_isUnit (s : σ) (ha : D.IsDistinguished (a s)) :
    IsUnit (derivedPDivisionVariable D a s) := by
  have hp := derivedPDivision_p_mem_jacobson D a
  apply (DeltaStructure.isDistinguished_factor (derivedDeltaDivisionStructure D (p : A) a)
    (p : C₀) (derivedPDivisionVariable D a s) ?_ hp hp).2
  rw [derivedPDivisionVariable_relation]
  exact (derivedDeltaDivisionMap_isDeltaHom D (p : A) a).map_isDistinguished ha

/-- 実導来候補における、指定変数像そのもので与えられる単元係数。 -/
theorem exists_derivedPDivision_unit_factor (s : σ) (ha : D.IsDistinguished (a s)) :
    ∃ u : C₀ˣ, (u : C₀) = derivedPDivisionVariable D a s ∧
      derivedDeltaDivisionMap D (p : A) a (a s) = p * (u : C₀) := by
  obtain ⟨u, hu⟩ := derivedPDivisionVariable_isUnit D a s ha
  exact ⟨u, hu, by rw [hu]; exact (derivedPDivisionVariable_relation D a s).symm⟩

end SerrePositivity.BhattScholze

end DeltaPDivisionDerivedUnit

/-! ## φ(y)/pとy^p/pの旧pねじれ除去商の比較

既存のp正則性とδ商普遍性によりraw平行移動を移す。
完備化後の平坦性・分冪構造はこの結果には含めない。
-/

@[expose] public noncomputable section DeltaPDivisionFrobeniusShiftTorsion

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

end DeltaPDivisionFrobeniusShiftTorsion

/-! ## p除算のFrobenius平行移動と実導来完備化H⁰

既存の実PD完備化の標準単位と一意延長を用いる。
古典的完備化への置換や導来pushoutの離散性を仮定しない。
-/

@[expose] public noncomputable section DeltaPDivisionFrobeniusShiftDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : σ → A)
attribute [local instance] derivedDeltaDivisionCommRing
local notation "aφ" => fun s ↦ D.frobeniusLift (y s)
local notation "apow" => fun s ↦ y s ^ p
local notation "Qφ" => DeltaDivisionTorsionQuotient D (p : A) aφ
local notation "Qpow" => DeltaDivisionTorsionQuotient D (p : A) apow
local notation "Hφ" => DerivedDeltaDivisionCompletion D (p : A) aφ
local notation "Hpow" => DerivedDeltaDivisionCompletion D (p : A) apow
local notation "Eφ" => derivedDeltaDivisionStructure D (p : A) aφ
local notation "Epow" => derivedDeltaDivisionStructure D (p : A) apow
local notation "qφ" => deltaDivisionTorsionMap D (p : A) aφ
local notation "qpow" => deltaDivisionTorsionMap D (p : A) apow
local notation "uφ" => pdCompletionUnit Qφ p (qφ (p : A))
local notation "upow" => pdCompletionUnit Qpow p (qpow (p : A))
local notation "jφ" => derivedDeltaDivisionMap D (p : A) aφ
local notation "jpow" => derivedDeltaDivisionMap D (p : A) apow

private theorem exists_derivedMap (a b : σ → A)
    (f : DeltaDivisionTorsionQuotient D (p : A) a →+* DeltaDivisionTorsionQuotient D (p : A) b)
    (hf : (deltaDivisionTorsionStructure D (p : A) a).IsDeltaHom
      (deltaDivisionTorsionStructure D (p : A) b) f)
    (hbase : f.comp (deltaDivisionTorsionMap D (p : A) a) =
      deltaDivisionTorsionMap D (p : A) b) :
    ∃! h : DerivedDeltaDivisionCompletion D (p : A) a →+*
        DerivedDeltaDivisionCompletion D (p : A) b,
      (derivedDeltaDivisionStructure D (p : A) a).IsDeltaHom
          (derivedDeltaDivisionStructure D (p : A) b) h ∧
        h.comp (pdCompletionUnit (DeltaDivisionTorsionQuotient D (p : A) a) p
          (deltaDivisionTorsionMap D (p : A) a (p : A))) =
        (pdCompletionUnit (DeltaDivisionTorsionQuotient D (p : A) b) p
          (deltaDivisionTorsionMap D (p : A) b (p : A))).comp f := by
  let Q := DeltaDivisionTorsionQuotient D (p : A) b
  let j := deltaDivisionTorsionMap D (p : A) b
  let u := pdCompletionUnit Q p (j (p : A))
  let g := u.comp f
  have hg := (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D (p : A) b)
    (j (p : A))).comp hf
  have hp := derivedDeltaDivision_complete_p D (p : A) b
  have hd : IsModuleComplete (DerivedDeltaDivisionCompletion D (p : A) b)
      (g (deltaDivisionTorsionMap D (p : A) a (p : A)))
      (ModuleCat.of (DerivedDeltaDivisionCompletion D (p : A) b)
        (DerivedDeltaDivisionCompletion D (p : A) b)) := by
    have he : g (deltaDivisionTorsionMap D (p : A) a (p : A)) =
        (p : DerivedDeltaDivisionCompletion D (p : A) b) := by
      change u (f (deltaDivisionTorsionMap D (p : A) a (p : A))) = _
      have hv : f (deltaDivisionTorsionMap D (p : A) a (p : A)) = j (p : A) :=
        RingHom.congr_fun hbase (p : A)
      exact (congrArg u hv).trans
        ((congrArg u (map_natCast j p)).trans (map_natCast u p))
    exact he.symm ▸ hp
  exact existsUnique_deltaPDCompletionHom (deltaDivisionTorsionStructure D (p : A) a)
    (deltaDivisionTorsionMap D (p : A) a (p : A))
    (derivedDeltaDivisionStructure D (p : A) b) g hg hp hd

/-- 正方向の旧ねじれ除去商の射は、実導来完備化H⁰へ一意に延長する。 -/
theorem existsUnique_deltaPDivisionDerivedFrobeniusToPower :
    ∃! f : Hφ →+* Hpow, (Eφ).IsDeltaHom Epow f ∧
      f.comp uφ = (upow).comp (deltaPDivisionTorsionFrobeniusToPower D y) :=
  exists_derivedMap D _ _ (deltaPDivisionTorsionFrobeniusToPower D y)
    (deltaPDivisionTorsionFrobeniusToPower_spec D y).1
    (deltaPDivisionTorsionFrobeniusToPower_spec D y).2

/-- 実導来完備化H⁰間の正方向の具体的標準射。 -/
def deltaPDivisionDerivedFrobeniusToPower : Hφ →+* Hpow :=
  (existsUnique_deltaPDivisionDerivedFrobeniusToPower D y).choose

/-- 正方向の射は実δ構造とKoszul標準単位を保つ。 -/
theorem deltaPDivisionDerivedFrobeniusToPower_spec :
    (Eφ).IsDeltaHom Epow (deltaPDivisionDerivedFrobeniusToPower D y) ∧
      (deltaPDivisionDerivedFrobeniusToPower D y).comp uφ =
        (upow).comp (deltaPDivisionTorsionFrobeniusToPower D y) :=
  (existsUnique_deltaPDivisionDerivedFrobeniusToPower D y).choose_spec.1

/-- 逆方向の旧ねじれ除去商の射も実導来完備化H⁰へ一意に延長する。 -/
theorem existsUnique_deltaPDivisionDerivedPowerToFrobenius :
    ∃! f : Hpow →+* Hφ, (Epow).IsDeltaHom Eφ f ∧
      f.comp upow = (uφ).comp (deltaPDivisionTorsionPowerToFrobenius D y) :=
  exists_derivedMap D _ _ (deltaPDivisionTorsionPowerToFrobenius D y)
    (deltaPDivisionTorsionPowerToFrobenius_spec D y).1
    (deltaPDivisionTorsionPowerToFrobenius_spec D y).2

/-- 実導来完備化H⁰間の逆方向の具体的標準射。 -/
def deltaPDivisionDerivedPowerToFrobenius : Hpow →+* Hφ :=
  (existsUnique_deltaPDivisionDerivedPowerToFrobenius D y).choose

/-- 逆方向の射も実δ構造とKoszul標準単位を保つ。 -/
theorem deltaPDivisionDerivedPowerToFrobenius_spec :
    (Epow).IsDeltaHom Eφ (deltaPDivisionDerivedPowerToFrobenius D y) ∧
      (deltaPDivisionDerivedPowerToFrobenius D y).comp upow =
        (uφ).comp (deltaPDivisionTorsionPowerToFrobenius D y) :=
  (existsUnique_deltaPDivisionDerivedPowerToFrobenius D y).choose_spec.1

/-- 実H⁰の正逆方向の合成は標準単位の一意延長性によって恒等射。 -/
theorem deltaPDivisionDerivedPowerToFrobenius_comp_toPower :
    (deltaPDivisionDerivedPowerToFrobenius D y).comp
      (deltaPDivisionDerivedFrobeniusToPower D y) = RingHom.id Hφ := by
  apply pdCompletionRingHom_ext Qφ p (qφ (p : A)) Hφ uφ
    (derivedDeltaDivision_complete_p D (p : A) aφ)
    (pdCompletionH0_self_complete_d Qφ p (qφ (p : A)))
  · rw [RingHom.comp_assoc, (deltaPDivisionDerivedFrobeniusToPower_spec D y).2,
      ← RingHom.comp_assoc, (deltaPDivisionDerivedPowerToFrobenius_spec D y).2,
      RingHom.comp_assoc, deltaPDivisionTorsionPowerToFrobenius_comp_toPower, RingHom.comp_id]
  · exact RingHom.id_comp _

/-- 実H⁰の逆順の合成も恒等射。 -/
theorem deltaPDivisionDerivedFrobeniusToPower_comp_toFrobenius :
    (deltaPDivisionDerivedFrobeniusToPower D y).comp
      (deltaPDivisionDerivedPowerToFrobenius D y) = RingHom.id Hpow := by
  apply pdCompletionRingHom_ext Qpow p (qpow (p : A)) Hpow upow
    (derivedDeltaDivision_complete_p D (p : A) apow)
    (pdCompletionH0_self_complete_d Qpow p (qpow (p : A)))
  · rw [RingHom.comp_assoc, (deltaPDivisionDerivedPowerToFrobenius_spec D y).2,
      ← RingHom.comp_assoc, (deltaPDivisionDerivedFrobeniusToPower_spec D y).2,
      RingHom.comp_assoc, deltaPDivisionTorsionFrobeniusToPower_comp_toFrobenius, RingHom.comp_id]
  · exact RingHom.id_comp _

/-- φ(y)/pとy^p/pの既存実導来完備化H⁰を結ぶ具体的同型。 -/
def deltaPDivisionFrobeniusShiftDerivedEquiv : Hφ ≃+* Hpow :=
  RingEquiv.ofRingHom (deltaPDivisionDerivedFrobeniusToPower D y)
    (deltaPDivisionDerivedPowerToFrobenius D y)
    (deltaPDivisionDerivedFrobeniusToPower_comp_toFrobenius D y)
    (deltaPDivisionDerivedPowerToFrobenius_comp_toPower D y)

/-- 実H⁰の同型の両方向は実δ構造と両立する。 -/
theorem deltaPDivisionFrobeniusShiftDerivedEquiv_isDeltaHom :
    (Eφ).IsDeltaHom Epow (deltaPDivisionFrobeniusShiftDerivedEquiv D y).toRingHom ∧
      (Epow).IsDeltaHom Eφ (deltaPDivisionFrobeniusShiftDerivedEquiv D y).symm.toRingHom :=
  ⟨(deltaPDivisionDerivedFrobeniusToPower_spec D y).1,
    (deltaPDivisionDerivedPowerToFrobenius_spec D y).1⟩

/-- 実H⁰同型は元の旧ねじれ除去商からの標準単位と両立する。 -/
theorem deltaPDivisionFrobeniusShiftDerivedEquiv_comp_unit :
    (deltaPDivisionFrobeniusShiftDerivedEquiv D y).toRingHom.comp uφ =
      (upow).comp (deltaPDivisionFrobeniusShiftTorsionEquiv D y).toRingHom :=
  (deltaPDivisionDerivedFrobeniusToPower_spec D y).2

/-- 実H⁰同型も元の基底環からの標準射を保つ。 -/
theorem deltaPDivisionFrobeniusShiftDerivedEquiv_comp :
    (deltaPDivisionFrobeniusShiftDerivedEquiv D y).toRingHom.comp jφ = jpow := by
  change (deltaPDivisionDerivedFrobeniusToPower D y).comp ((uφ).comp qφ) = (upow).comp qpow
  rw [← RingHom.comp_assoc, (deltaPDivisionDerivedFrobeniusToPower_spec D y).2,
    RingHom.comp_assoc, (deltaPDivisionTorsionFrobeniusToPower_spec D y).2]

end SerrePositivity.BhattScholze

end DeltaPDivisionFrobeniusShiftDerived

/-! ## 古典的p除算候補におけるdistinguished元の単元係数

既存BS 著者版 Lemma 2.24を具体的な候補と標準射へ適用する。
実導来完備化との比較や完全平坦性はこの計算の結論に含めない。
-/

@[expose] public noncomputable section DeltaPDivisionUnit

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p除算候補の二元表示の完備化イデアルは、実際にはpの主イデアル。 -/
theorem deltaPDivisionAdicIdeal_eq_span_p (D : DeltaStructure p A) (a : σ → A) :
    deltaDivisionAdicIdeal D (p : A) a =
      Ideal.span {(p : DeltaDivisionTorsionQuotient D (p : A) a)} := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  exact (congrArg (fun b : B ↦ Ideal.span {(p : B), b})
    (map_natCast (deltaDivisionTorsionMap D (p : A) a) p)).trans
      (congrArg (Ideal.span : Set B → Ideal B)
        (Set.insert_eq_of_mem (Set.mem_singleton (p : B))))

/-- 古典的p除算候補はp進完備。二元表示のイデアルから正確に移送する。 -/
theorem classicalPDivision_isAdicComplete (D : DeltaStructure p A) (a : σ → A) :
    IsAdicComplete (Ideal.span {(p : ClassicalDeltaDivisionCompletion D (p : A) a)})
      (ClassicalDeltaDivisionCompletion D (p : A) a) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  let I := deltaDivisionAdicIdeal D (p : A) a
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  have hc := AdicCompletion.isAdicComplete_self I (deltaDivisionAdicIdeal_fg D (p : A) a)
  have hmap : I.map (algebraMap B C) = Ideal.span {(p : C)} := by
    calc
      _ = (Ideal.span {(p : B)}).map (algebraMap B C) :=
        congrArg (fun J : Ideal B ↦ J.map (algebraMap B C))
          (deltaPDivisionAdicIdeal_eq_span_p D a)
      _ = Ideal.span {algebraMap B C (p : B)} := by rw [Ideal.map_span, Set.image_singleton]
      _ = _ := congrArg (fun c : C ↦ Ideal.span {c}) (map_natCast (algebraMap B C) p)
  exact hmap ▸ hc

/-- p正則な旧ねじれ除去商のp進完備化にも新しいpねじれは生じない。 -/
theorem classicalPDivision_p_mul_injective (D : DeltaStructure p A) (a : σ → A) :
    Function.Injective (fun x : ClassicalDeltaDivisionCompletion D (p : A) a ↦
      (p : ClassicalDeltaDivisionCompletion D (p : A) a) * x) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  have hpB : IsSMulRegular B (p : B) := deltaDivisionTorsionQuotient_p_mul_injective D a
  have aux (J : Ideal B) (hJ : J = Ideal.span {(p : B)}) :
      IsSMulRegular (AdicCompletion J B) (algebraMap B (AdicCompletion J B) (p : B)) := by
    subst J
    exact SerrePositivity.isSMulRegular_adicCompletion_span_singleton B (p : B) hpB
  have h := aux (deltaDivisionAdicIdeal D (p : A) a) (deltaPDivisionAdicIdeal_eq_span_p D a)
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  exact Eq.mp (congrArg (fun c : C ↦ IsSMulRegular C c) (map_natCast (algebraMap B C) p)) h

/-- この古典的候補自身の導来p完備性。p正則性を証明して既存比較を適用する。 -/
theorem classicalPDivision_isModuleComplete (D : DeltaStructure p A) (a : σ → A) :
    SerrePositivity.DerivedCompletion.IsModuleComplete
      (ClassicalDeltaDivisionCompletion D (p : A) a)
      (p : ClassicalDeltaDivisionCompletion D (p : A) a)
      (ModuleCat.of (ClassicalDeltaDivisionCompletion D (p : A) a)
        (ClassicalDeltaDivisionCompletion D (p : A) a)) :=
  (SerrePositivity.DerivedCompletion.isRingModuleComplete_iff_isAdicComplete_natCast
    _ p (classicalPDivision_p_mul_injective D a)).mpr (classicalPDivision_isAdicComplete D a)

/-- p除算変数の既存古典的完備化への標準像。 -/
def classicalPDivisionVariable (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    ClassicalDeltaDivisionCompletion D (p : A) a :=
  algebraMap (DeltaDivisionTorsionQuotient D (p : A) a) _
    (Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D (p : A) a s))

/-- p除算変数の標準像とpとの積は指定元の像。 -/
theorem classicalPDivisionVariable_relation (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) * classicalPDivisionVariable D a s =
      classicalDeltaDivisionMap D (p : A) a (a s) := by
  let q : DeltaAdjoinDivision D (p : A) a →+* DeltaDivisionTorsionQuotient D (p : A) a :=
    Ideal.Quotient.mk _
  let k := (algebraMap (DeltaDivisionTorsionQuotient D (p : A) a)
    (ClassicalDeltaDivisionCompletion D (p : A) a)).comp q
  have h := congrArg k (deltaAdjoinDivision_relation D (p : A) a s)
  simpa only [k, q, classicalPDivisionVariable, classicalDeltaDivisionMap,
    deltaDivisionTorsionMap, RingHom.comp_apply, map_mul, map_natCast] using h

/-- 具体的な古典的p除算候補ではpはJacobson根基に属する。 -/
theorem classicalPDivision_p_mem_jacobson (D : DeltaStructure p A) (a : σ → A) :
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) ∈ Ideal.jacobson (⊥ : Ideal _) := by
  let B := DeltaDivisionTorsionQuotient D (p : A) a
  let I := deltaDivisionAdicIdeal D (p : A) a
  let C := ClassicalDeltaDivisionCompletion D (p : A) a
  let : IsAdicComplete (I.map (algebraMap B C)) C :=
    AdicCompletion.isAdicComplete_self I (deltaDivisionAdicIdeal_fg D (p : A) a)
  apply IsAdicComplete.le_jacobson_bot (I.map (algebraMap B C))
  have hp : (p : B) ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  change (p : C) ∈ (I.map (algebraMap B C) : Ideal C)
  have hm := Ideal.mem_map_of_mem (algebraMap B C) hp
  exact Eq.mp (congrArg (fun c : C ↦ c ∈ (I.map (algebraMap B C) : Ideal C))
    (map_natCast (algebraMap B C) p)) hm

/-- 指定元がdistinguishedなら、古典的p除算候補内の具体的な除算変数像は単元。 -/
theorem classicalPDivisionVariable_isUnit (D : DeltaStructure p A) (a : σ → A) (s : σ)
    (ha : D.IsDistinguished (a s)) : IsUnit (classicalPDivisionVariable D a s) := by
  have hp := classicalPDivision_p_mem_jacobson D a
  apply (DeltaStructure.isDistinguished_factor (classicalDeltaDivisionStructure D (p : A) a)
    (p : ClassicalDeltaDivisionCompletion D (p : A) a) (classicalPDivisionVariable D a s)
    ?_ hp hp).2
  rw [classicalPDivisionVariable_relation]
  exact (classicalDeltaDivisionMap_isDeltaHom D (p : A) a).map_isDistinguished ha

/-- 原典BS 著者版 Proposition 3.13のφ(y)=p*u型の具体的な単元係数（古典的候補での結果）。 -/
theorem exists_classicalPDivision_unit_factor (D : DeltaStructure p A) (a : σ → A) (s : σ)
    (ha : D.IsDistinguished (a s)) :
    ∃ u : (ClassicalDeltaDivisionCompletion D (p : A) a)ˣ,
      (u : ClassicalDeltaDivisionCompletion D (p : A) a) = classicalPDivisionVariable D a s ∧
      classicalDeltaDivisionMap D (p : A) a (a s) = p * (u : _) := by
  obtain ⟨u, hu⟩ := classicalPDivisionVariable_isUnit D a s ha
  exact ⟨u, hu, by rw [hu]; exact (classicalPDivisionVariable_relation D a s).symm⟩

end SerrePositivity.BhattScholze

end DeltaPDivisionUnit
