module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShiftTorsion
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionPDCompletion

/-! # p除算のFrobenius平行移動と実導来完備化H⁰

既存の実PD完備化の標準単位と一意延長を用いる。
古典的完備化への置換や導来pushoutの離散性を仮定しない。
-/

@[expose] public noncomputable section
universe u
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
