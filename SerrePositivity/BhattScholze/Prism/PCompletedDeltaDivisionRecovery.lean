module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaDivisionComparison
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius

/-! # 既に可除な完全p進完備δ環の除算候補からの復元

distinguished元dについて指定元族が既にdで割り切れる完全p進完備δ環では、
p進完備δ除算候補への標準射が同型。実導来(p,d)完備化の反復とは区別する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}
variable (D : DeltaStructure p R) (hD : D.IsPerfect)
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable (d : R) (hd : D.IsDistinguished d) (a : σ → R) (ha : ∀ s, d ∣ a s)

/-- 恒等基底射を一意に延長して得る、具体的な除算候補からの復元射。 -/
def pCompletedDeltaDivisionRetract : PCompletedDeltaDivision D d a →+* R :=
  (existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose

/-- 復元射はδ射。 -/
theorem pCompletedDeltaDivisionRetract_isDeltaHom :
    (pCompletedDeltaDivisionStructure D d a).IsDeltaHom D
      (pCompletedDeltaDivisionRetract D hD d hd a ha) :=
  (existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose_spec.1.1

/-- 復元射と元の標準射の合成は恒等射。 -/
@[simp] theorem pCompletedDeltaDivisionRetract_comp_base :
    (pCompletedDeltaDivisionRetract D hD d hd a ha).comp (pCompletedDeltaDivisionMap D d a) =
      RingHom.id R :=
  (existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose_spec.1.2

/-- 標準射と復元射の逆順の合成も恒等射。 -/
@[simp] theorem pCompletedDeltaDivisionMap_comp_retract :
    (pCompletedDeltaDivisionMap D d a).comp (pCompletedDeltaDivisionRetract D hD d hd a ha) =
      RingHom.id (PCompletedDeltaDivision D d a) := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  apply pCompletedDeltaDivisionHom_ext D _ (pCompletedDeltaDivision_isPerfect D d a) d hd a
    _ _ ((pCompletedDeltaDivisionMap_isDeltaHom D d a).comp
      (pCompletedDeltaDivisionRetract_isDeltaHom D hD d hd a ha))
    (pCompletedDeltaDivisionStructure D d a).isDeltaHom_id
  rw [RingHom.comp_assoc, pCompletedDeltaDivisionRetract_comp_base,
    RingHom.comp_id, RingHom.id_comp]

include hD hd ha in
/-- 既に完全p進完備で、指定元族がdで可除なδ環の標準除算候補射は全単射。 -/
theorem pCompletedDeltaDivisionMap_bijective_of_dvd :
    Function.Bijective (pCompletedDeltaDivisionMap D d a) := by
  have hl : Function.LeftInverse (pCompletedDeltaDivisionRetract D hD d hd a ha)
      (pCompletedDeltaDivisionMap D d a) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaDivisionRetract_comp_base D hD d hd a ha) x
  have hr : Function.RightInverse (pCompletedDeltaDivisionRetract D hD d hd a ha)
      (pCompletedDeltaDivisionMap D d a) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaDivisionMap_comp_retract D hD d hd a ha) x
  exact ⟨hl.injective, hr.surjective⟩

/-- 完全p進完備な可除δ環と、その具体的なp進完備δ除算候補の同型。 -/
def pCompletedDeltaDivisionRecoveryEquiv : R ≃+* PCompletedDeltaDivision D d a :=
  RingEquiv.ofBijective (pCompletedDeltaDivisionMap D d a)
    (pCompletedDeltaDivisionMap_bijective_of_dvd D hD d hd a ha)

/-- 復元同型の順射は標準除算候補射。 -/
@[simp] theorem pCompletedDeltaDivisionRecoveryEquiv_toRingHom :
    (pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).toRingHom =
      pCompletedDeltaDivisionMap D d a := rfl

/-- 復元同型の逆射は選んだ具体的な復元射。 -/
@[simp] theorem pCompletedDeltaDivisionRecoveryEquiv_symm_toRingHom :
    (pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm.toRingHom =
      pCompletedDeltaDivisionRetract D hD d hd a ha := by
  apply RingHom.ext
  intro x
  apply (pCompletedDeltaDivisionMap_bijective_of_dvd D hD d hd a ha).1
  change (pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha)
    ((pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm x) =
      pCompletedDeltaDivisionMap D d a (pCompletedDeltaDivisionRetract D hD d hd a ha x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (pCompletedDeltaDivisionMap_comp_retract D hD d hd a ha) x).symm

/-- 復元同型の逆射もδ射。 -/
theorem pCompletedDeltaDivisionRecoveryEquiv_symm_isDeltaHom :
    (pCompletedDeltaDivisionStructure D d a).IsDeltaHom D
      (pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm.toRingHom := by
  rw [pCompletedDeltaDivisionRecoveryEquiv_symm_toRingHom]
  exact pCompletedDeltaDivisionRetract_isDeltaHom D hD d hd a ha

end SerrePositivity.BhattScholze
