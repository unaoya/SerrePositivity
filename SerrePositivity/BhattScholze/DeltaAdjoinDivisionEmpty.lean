module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionSum

/-! # 空族のraw δ除算包は元の係数δ環 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v} [IsEmpty σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "B" => DeltaAdjoinDivision D d a
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "j" => deltaAdjoinDivisionMap D d a

/-- 空族raw包から係数δ環への標準射の普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionEmptyEval :
    ∃! f : B →+* A, (DB).IsDeltaHom D f ∧ f.comp j = RingHom.id A ∧
      ∀ s, f (deltaAdjoinDivisionVariable D d a s) = isEmptyElim s := by
  apply existsUnique_deltaAdjoinDivisionHom D D d a (RingHom.id A) D.isDeltaHom_id
  intro s
  exact isEmptyElim s

/-- 空族raw包の標準評価射。 -/
def deltaAdjoinDivisionEmptyEval : B →+* A :=
  (existsUnique_deltaAdjoinDivisionEmptyEval D d a).choose

/-- 空族評価射はδと係数を保つ。 -/
theorem deltaAdjoinDivisionEmptyEval_spec :
    (DB).IsDeltaHom D (deltaAdjoinDivisionEmptyEval D d a) ∧
      (deltaAdjoinDivisionEmptyEval D d a).comp j = RingHom.id A := by
  have h := (existsUnique_deltaAdjoinDivisionEmptyEval D d a).choose_spec.1
  exact ⟨h.1, h.2.1⟩

/-- 空族では係数射と標準評価射の逆順合成も恒等射。 -/
theorem deltaAdjoinDivisionMap_comp_emptyEval :
    (j).comp (deltaAdjoinDivisionEmptyEval D d a) = RingHom.id B := by
  have h := deltaAdjoinDivisionEmptyEval_spec D d a
  apply deltaAdjoinDivisionHom_ext D DB d a _ _
    ((deltaAdjoinDivisionMap_isDeltaHom D d a).comp h.1) (DB).isDeltaHom_id
  · rw [RingHom.comp_assoc, h.2, RingHom.comp_id, RingHom.id_comp]
  · intro s
    exact isEmptyElim s

/-- 空族raw包と元の係数環の標準同型。 -/
def deltaAdjoinDivisionEmptyEquiv : B ≃+* A :=
  RingEquiv.ofRingHom (deltaAdjoinDivisionEmptyEval D d a) j
    (deltaAdjoinDivisionEmptyEval_spec D d a).2 (deltaAdjoinDivisionMap_comp_emptyEval D d a)

/-- 空族比較同型の両方向はδ射。 -/
theorem deltaAdjoinDivisionEmptyEquiv_isDeltaHom :
    (DB).IsDeltaHom D (deltaAdjoinDivisionEmptyEquiv D d a).toRingHom ∧
      D.IsDeltaHom DB (deltaAdjoinDivisionEmptyEquiv D d a).symm.toRingHom :=
  ⟨(deltaAdjoinDivisionEmptyEval_spec D d a).1, deltaAdjoinDivisionMap_isDeltaHom D d a⟩

/-- 空族比較同型は標準係数射の逆。 -/
theorem deltaAdjoinDivisionEmptyEquiv_coeff (x : A) :
    deltaAdjoinDivisionEmptyEquiv D d a (j x) = x :=
  DFunLike.congr_fun (deltaAdjoinDivisionEmptyEval_spec D d a).2 x

end SerrePositivity.BhattScholze
