module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivision

/-! # 同時族と二段raw δ除算の標準同型

指定した除算解についての既存普遍性を用いる。非零因子性や平坦性は不要。
-/

@[expose] public noncomputable section
universe u v w z
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v} {τ : Type w}

/-- δ除算包のδ射は係数と初期除算変数で決まる。 -/
theorem deltaAdjoinDivisionHom_ext {C : Type z} [CommRing C]
    (D : DeltaStructure p A) (E : DeltaStructure p C) (d : A) (a : σ → A)
    (f g : DeltaAdjoinDivision D d a →+* C)
    (hf : (deltaAdjoinDivisionStructure D d a).IsDeltaHom E f)
    (hg : (deltaAdjoinDivisionStructure D d a).IsDeltaHom E g)
    (hb : f.comp (deltaAdjoinDivisionMap D d a) = g.comp (deltaAdjoinDivisionMap D d a))
    (hv : ∀ s, f (deltaAdjoinDivisionVariable D d a s) =
      g (deltaAdjoinDivisionVariable D d a s)) : f = g := by
  obtain ⟨k, _, hu⟩ := existsUnique_deltaAdjoinDivisionHom D E d a
    (f.comp (deltaAdjoinDivisionMap D d a))
    (hf.comp (deltaAdjoinDivisionMap_isDeltaHom D d a))
    (fun s ↦ f (deltaAdjoinDivisionVariable D d a s)) (fun s ↦ by
      simpa only [RingHom.comp_apply, map_mul] using
        congrArg f (deltaAdjoinDivision_relation D d a s))
  exact (hu f ⟨hf, rfl, fun _ ↦ rfl⟩).trans (hu g ⟨hg, hb.symm, fun s ↦ (hv s).symm⟩).symm

variable (D : DeltaStructure p A) (d : A) (a : σ → A) (b : τ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "E" => deltaAdjoinDivisionStructure D d a
local notation "j" => deltaAdjoinDivisionMap D d a
local notation "vL" => deltaAdjoinDivisionVariable D d a
local notation "S" => DeltaAdjoinDivision D d (Sum.elim a b)
local notation "DS" => deltaAdjoinDivisionStructure D d (Sum.elim a b)
local notation "q" => deltaAdjoinDivisionMap D d (Sum.elim a b)
local notation "vS" => deltaAdjoinDivisionVariable D d (Sum.elim a b)
local notation "T" => DeltaAdjoinDivision E (j d) (fun t ↦ j (b t))
local notation "DT" => deltaAdjoinDivisionStructure E (j d) (fun t ↦ j (b t))
local notation "k" => deltaAdjoinDivisionMap E (j d) (fun t ↦ j (b t))
local notation "vT" => deltaAdjoinDivisionVariable E (j d) (fun t ↦ j (b t))

/-- 同時除算包への第一段の標準δ射を指定する普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionLeftToSum :
    ∃! f : L →+* S, (E).IsDeltaHom DS f ∧ f.comp j = q ∧
      ∀ s, f (vL s) = vS (Sum.inl s) := by
  apply existsUnique_deltaAdjoinDivisionHom D DS d a q
    (deltaAdjoinDivisionMap_isDeltaHom D d (Sum.elim a b))
  intro s
  exact deltaAdjoinDivision_relation D d (Sum.elim a b) (Sum.inl s)

/-- 第一段から同時除算包への標準δ射。 -/
def deltaAdjoinDivisionLeftToSum : L →+* S :=
  (existsUnique_deltaAdjoinDivisionLeftToSum D d a b).choose

/-- 第一段の標準射のδ・係数・変数の公式。 -/
theorem deltaAdjoinDivisionLeftToSum_spec :
    (E).IsDeltaHom DS (deltaAdjoinDivisionLeftToSum D d a b) ∧
      (deltaAdjoinDivisionLeftToSum D d a b).comp j = q ∧
      ∀ s, deltaAdjoinDivisionLeftToSum D d a b (vL s) = vS (Sum.inl s) :=
  (existsUnique_deltaAdjoinDivisionLeftToSum D d a b).choose_spec.1

/-- 二段除算包から同時除算包へのδ射を指定する普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionIteratedToSum :
    ∃! f : T →+* S, (DT).IsDeltaHom DS f ∧
      f.comp k = deltaAdjoinDivisionLeftToSum D d a b ∧
      ∀ t, f (vT t) = vS (Sum.inr t) := by
  let f := deltaAdjoinDivisionLeftToSum D d a b
  have hf := deltaAdjoinDivisionLeftToSum_spec D d a b
  apply existsUnique_deltaAdjoinDivisionHom E DS (j d) (fun t ↦ j (b t)) f hf.1
  intro t
  have hd := DFunLike.congr_fun hf.2.1 d
  have hb := DFunLike.congr_fun hf.2.1 (b t)
  change f (j d) = q d at hd
  change f (j (b t)) = q (b t) at hb
  rw [hd, hb]
  exact deltaAdjoinDivision_relation D d (Sum.elim a b) (Sum.inr t)

/-- 二段から同時除算への標準δ射。 -/
def deltaAdjoinDivisionIteratedToSum : T →+* S :=
  (existsUnique_deltaAdjoinDivisionIteratedToSum D d a b).choose

/-- 二段から同時除算への射のδ・第一段係数・右変数の公式。 -/
theorem deltaAdjoinDivisionIteratedToSum_spec :
    (DT).IsDeltaHom DS (deltaAdjoinDivisionIteratedToSum D d a b) ∧
      (deltaAdjoinDivisionIteratedToSum D d a b).comp k = deltaAdjoinDivisionLeftToSum D d a b ∧
      ∀ t, deltaAdjoinDivisionIteratedToSum D d a b (vT t) = vS (Sum.inr t) :=
  (existsUnique_deltaAdjoinDivisionIteratedToSum D d a b).choose_spec.1

/-- 同時除算から二段除算へのδ射を指定する普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionSumToIterated :
    ∃! f : S →+* T, (DS).IsDeltaHom DT f ∧ f.comp q = (k).comp j ∧
      ∀ s, f (vS s) = Sum.elim (fun s ↦ k (vL s)) vT s := by
  apply existsUnique_deltaAdjoinDivisionHom D DT d (Sum.elim a b) ((k).comp j)
    ((deltaAdjoinDivisionMap_isDeltaHom E (j d) (fun t ↦ j (b t))).comp
      (deltaAdjoinDivisionMap_isDeltaHom D d a))
  intro s
  cases s with
  | inl s =>
    change k (j d) * k (vL s) = k (j (a s))
    rw [← map_mul, deltaAdjoinDivision_relation]
  | inr t =>
    exact deltaAdjoinDivision_relation E (j d) (fun t ↦ j (b t)) t

/-- 同時から二段除算への標準δ射。 -/
def deltaAdjoinDivisionSumToIterated : S →+* T :=
  (existsUnique_deltaAdjoinDivisionSumToIterated D d a b).choose

/-- 同時から二段除算への射のδ・係数・左右変数の公式。 -/
theorem deltaAdjoinDivisionSumToIterated_spec :
    (DS).IsDeltaHom DT (deltaAdjoinDivisionSumToIterated D d a b) ∧
      (deltaAdjoinDivisionSumToIterated D d a b).comp q = (k).comp j ∧
      ∀ s, deltaAdjoinDivisionSumToIterated D d a b (vS s) =
        Sum.elim (fun s ↦ k (vL s)) vT s :=
  (existsUnique_deltaAdjoinDivisionSumToIterated D d a b).choose_spec.1

/-- 往復写像は第一段の標準射を保つ。 -/
theorem deltaAdjoinDivisionSumToIterated_comp_left :
    (deltaAdjoinDivisionSumToIterated D d a b).comp
      (deltaAdjoinDivisionLeftToSum D d a b) = k := by
  have hf := deltaAdjoinDivisionLeftToSum_spec D d a b
  have hh := deltaAdjoinDivisionSumToIterated_spec D d a b
  apply deltaAdjoinDivisionHom_ext D DT d a _ _ (hh.1.comp hf.1)
    (deltaAdjoinDivisionMap_isDeltaHom E (j d) (fun t ↦ j (b t)))
  · rw [RingHom.comp_assoc, hf.2.1, hh.2.1]
  · intro s
    rw [RingHom.comp_apply, hf.2.2, hh.2.2]
    rfl

/-- 同時除算包上での往復は恒等射。 -/
theorem deltaAdjoinDivisionIteratedToSum_comp_toIterated :
    (deltaAdjoinDivisionIteratedToSum D d a b).comp
      (deltaAdjoinDivisionSumToIterated D d a b) = RingHom.id S := by
  have hf := deltaAdjoinDivisionLeftToSum_spec D d a b
  have hg := deltaAdjoinDivisionIteratedToSum_spec D d a b
  have hh := deltaAdjoinDivisionSumToIterated_spec D d a b
  apply deltaAdjoinDivisionHom_ext D DS d (Sum.elim a b) _ _ (hg.1.comp hh.1) (DS).isDeltaHom_id
  · rw [RingHom.comp_assoc, hh.2.1, ← RingHom.comp_assoc, hg.2.1, hf.2.1,
      RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, hh.2.2]
    cases s with
    | inl s =>
      change deltaAdjoinDivisionIteratedToSum D d a b (k (vL s)) = vS (Sum.inl s)
      exact (DFunLike.congr_fun hg.2.1 (vL s)).trans (hf.2.2 s)
    | inr t => exact hg.2.2 t

/-- 二段除算包上での往復も恒等射。 -/
theorem deltaAdjoinDivisionSumToIterated_comp_toSum :
    (deltaAdjoinDivisionSumToIterated D d a b).comp
      (deltaAdjoinDivisionIteratedToSum D d a b) = RingHom.id T := by
  have hg := deltaAdjoinDivisionIteratedToSum_spec D d a b
  have hh := deltaAdjoinDivisionSumToIterated_spec D d a b
  apply deltaAdjoinDivisionHom_ext E DT (j d) (fun t ↦ j (b t)) _ _
    (hh.1.comp hg.1) (DT).isDeltaHom_id
  · rw [RingHom.comp_assoc, hg.2.1, deltaAdjoinDivisionSumToIterated_comp_left,
      RingHom.id_comp]
  · intro t
    rw [RingHom.comp_apply, hg.2.2, hh.2.2]
    rfl

/-- 任意元族の同時raw除算と二段raw除算の具体的な環同型。 -/
def deltaAdjoinDivisionSumEquiv : S ≃+* T :=
  RingEquiv.ofRingHom (deltaAdjoinDivisionSumToIterated D d a b)
    (deltaAdjoinDivisionIteratedToSum D d a b)
    (deltaAdjoinDivisionSumToIterated_comp_toSum D d a b)
    (deltaAdjoinDivisionIteratedToSum_comp_toIterated D d a b)

/-- 標準同型の両方向はδ構造を保つ。 -/
theorem deltaAdjoinDivisionSumEquiv_isDeltaHom :
    (DS).IsDeltaHom DT (deltaAdjoinDivisionSumEquiv D d a b).toRingHom ∧
      (DT).IsDeltaHom DS (deltaAdjoinDivisionSumEquiv D d a b).symm.toRingHom :=
  ⟨(deltaAdjoinDivisionSumToIterated_spec D d a b).1,
    (deltaAdjoinDivisionIteratedToSum_spec D d a b).1⟩

/-- 標準同型は元の係数射を保つ。 -/
theorem deltaAdjoinDivisionSumEquiv_comp :
    (deltaAdjoinDivisionSumEquiv D d a b).toRingHom.comp q = (k).comp j :=
  (deltaAdjoinDivisionSumToIterated_spec D d a b).2.1

/-- 左族の除算変数は第一段の変数の標準像へ送られる。 -/
theorem deltaAdjoinDivisionSumEquiv_variable_inl (s : σ) :
    deltaAdjoinDivisionSumEquiv D d a b (vS (Sum.inl s)) = k (vL s) :=
  (deltaAdjoinDivisionSumToIterated_spec D d a b).2.2 (Sum.inl s)

/-- 右族の除算変数は第二段の除算変数へ送られる。 -/
theorem deltaAdjoinDivisionSumEquiv_variable_inr (t : τ) :
    deltaAdjoinDivisionSumEquiv D d a b (vS (Sum.inr t)) = vT t :=
  (deltaAdjoinDivisionSumToIterated_spec D d a b).2.2 (Sum.inr t)

end SerrePositivity.BhattScholze
