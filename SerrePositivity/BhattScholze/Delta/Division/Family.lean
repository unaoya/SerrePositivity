module

public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import Mathlib.Algebra.Colimit.DirectLimit
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaColimit

/-!
# δ 包の族：空の族、有限部分族の余極限、再添字付け、二段の除算

## 概要
空の族の raw 包は元の δ 環であること、有限部分族の raw 包の有向系とその環余極限が全族の raw 包と δ 同型であること、再添字付けとその恒等・合成公式、同時の族の除算と二段の除算の標準同型。
BS 著者版 Proposition 3.13 と Proposition 7.2 の包の構成に使う、δ 除算の族と有限部分族を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`、`Andre/Envelope/RootFamilyRaw`、`Andre/PowerRootEnvelope/DeltaDivisionWitt`、`Delta/DividedPower/PDivisionCompletion`、`Delta/Division/Source`。
-/

universe u v w z

/-! ## 同時族と二段raw δ除算の標準同型

指定した除算解についての既存普遍性を用いる。非零因子性や平坦性は不要。
-/

@[expose] public noncomputable section DeltaAdjoinDivisionSum

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

end DeltaAdjoinDivisionSum

/-! ## raw δ除算包の再添字付け -/

@[expose] public noncomputable section DeltaAdjoinDivisionReindex

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v} {τ : Type w}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (b : τ → A)
local notation "B" => DeltaAdjoinDivision D d a
local notation "C" => DeltaAdjoinDivision D d b
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "DC" => deltaAdjoinDivisionStructure D d b
local notation "jB" => deltaAdjoinDivisionMap D d a
local notation "jC" => deltaAdjoinDivisionMap D d b
local notation "vB" => deltaAdjoinDivisionVariable D d a
local notation "vC" => deltaAdjoinDivisionVariable D d b

/-- 添字写像と入力の一致で指定される標準δ射の普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionReindex (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) :
    ∃! f : B →+* C, (DB).IsDeltaHom DC f ∧ f.comp jB = jC ∧
      ∀ s, f (vB s) = vC (ρ s) := by
  apply existsUnique_deltaAdjoinDivisionHom D DC d a jC
    (deltaAdjoinDivisionMap_isDeltaHom D d b)
  intro s
  rw [h s]
  exact deltaAdjoinDivision_relation D d b (ρ s)

/-- 再添字付けによる具体的raw除算δ射。 -/
def deltaAdjoinDivisionReindex (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) : B →+* C :=
  (existsUnique_deltaAdjoinDivisionReindex D d a b ρ h).choose

/-- 再添字付け射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionReindex_spec (ρ : σ → τ) (h : ∀ s, a s = b (ρ s)) :
    (DB).IsDeltaHom DC (deltaAdjoinDivisionReindex D d a b ρ h) ∧
      (deltaAdjoinDivisionReindex D d a b ρ h).comp jB = jC ∧
      ∀ s, deltaAdjoinDivisionReindex D d a b ρ h (vB s) = vC (ρ s) :=
  (existsUnique_deltaAdjoinDivisionReindex D d a b ρ h).choose_spec.1

/-- 添字同値の逆方向を続けると恒等射となる。 -/
theorem deltaAdjoinDivisionReindex_symm_comp (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindex D d b a e.symm
      (fun t ↦ by rw [h, e.apply_symm_apply])).comp
      (deltaAdjoinDivisionReindex D d a b e h) = RingHom.id B := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b e h
  have hg := deltaAdjoinDivisionReindex_spec D d b a e.symm
    (fun t ↦ by rw [h, e.apply_symm_apply])
  apply deltaAdjoinDivisionHom_ext D DB d a _ _ (hg.1.comp hf.1) (DB).isDeltaHom_id
  · rw [RingHom.comp_assoc, hf.2.1, hg.2.1, RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, hf.2.2, hg.2.2, e.symm_apply_apply]
    rfl

/-- 逆順の再添字付けも恒等射となる。 -/
theorem deltaAdjoinDivisionReindex_comp_symm (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindex D d a b e h).comp
      (deltaAdjoinDivisionReindex D d b a e.symm
        (fun t ↦ by rw [h, e.apply_symm_apply])) = RingHom.id C := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b e h
  have hg := deltaAdjoinDivisionReindex_spec D d b a e.symm
    (fun t ↦ by rw [h, e.apply_symm_apply])
  apply deltaAdjoinDivisionHom_ext D DC d b _ _ (hf.1.comp hg.1) (DC).isDeltaHom_id
  · rw [RingHom.comp_assoc, hg.2.1, hf.2.1, RingHom.id_comp]
  · intro t
    rw [RingHom.comp_apply, hg.2.2, hf.2.2, e.apply_symm_apply]
    rfl

/-- 添字同値は係数と除算変数を保つ標準raw環同型を誘導する。 -/
def deltaAdjoinDivisionReindexEquiv (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) : B ≃+* C :=
  RingEquiv.ofRingHom (deltaAdjoinDivisionReindex D d a b e h)
    (deltaAdjoinDivisionReindex D d b a e.symm (fun t ↦ by rw [h, e.apply_symm_apply]))
    (deltaAdjoinDivisionReindex_comp_symm D d a b e h)
    (deltaAdjoinDivisionReindex_symm_comp D d a b e h)

/-- 再添字同型の両方向はδ構造を保つ。 -/
theorem deltaAdjoinDivisionReindexEquiv_isDeltaHom (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (DB).IsDeltaHom DC (deltaAdjoinDivisionReindexEquiv D d a b e h).toRingHom ∧
      (DC).IsDeltaHom DB (deltaAdjoinDivisionReindexEquiv D d a b e h).symm.toRingHom :=
  ⟨(deltaAdjoinDivisionReindex_spec D d a b e h).1,
    (deltaAdjoinDivisionReindex_spec D d b a e.symm
      (fun t ↦ by rw [h, e.apply_symm_apply])).1⟩

/-- 再添字同型は係数の標準射を保つ。 -/
theorem deltaAdjoinDivisionReindexEquiv_comp (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) :
    (deltaAdjoinDivisionReindexEquiv D d a b e h).toRingHom.comp jB = jC :=
  (deltaAdjoinDivisionReindex_spec D d a b e h).2.1

/-- 再添字同型の初期変数上の公式。 -/
theorem deltaAdjoinDivisionReindexEquiv_variable (e : σ ≃ τ) (h : ∀ s, a s = b (e s)) (s : σ) :
    deltaAdjoinDivisionReindexEquiv D d a b e h (vB s) = vC (e s) :=
  (deltaAdjoinDivisionReindex_spec D d a b e h).2.2 s

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionReindex

/-! ## 空族のraw δ除算包は元の係数δ環 -/

@[expose] public noncomputable section DeltaAdjoinDivisionEmpty

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

end DeltaAdjoinDivisionEmpty

/-! ## raw再添字射の恒等・合成公式 -/

@[expose] public noncomputable section DeltaAdjoinDivisionReindexFunctorial

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable {σ : Type v} {τ : Type w} {υ : Type z}
variable (D : DeltaStructure p A) (d : A)

/-- 恒等添字写像に沿うraw再添字射は恒等射。 -/
theorem deltaAdjoinDivisionReindex_id (a : σ → A) :
    deltaAdjoinDivisionReindex D d a a id (fun _ ↦ rfl) =
      RingHom.id (DeltaAdjoinDivision D d a) := by
  have h := deltaAdjoinDivisionReindex_spec D d a a id (fun _ ↦ rfl)
  apply deltaAdjoinDivisionHom_ext D (deltaAdjoinDivisionStructure D d a) d a _ _
    h.1 (deltaAdjoinDivisionStructure D d a).isDeltaHom_id
  · rw [h.2.1, RingHom.id_comp]
  · intro s
    exact h.2.2 s

/-- raw再添字射の合成は、添字写像の合成に沿う標準射。 -/
theorem deltaAdjoinDivisionReindex_comp (a : σ → A) (b : τ → A) (c : υ → A)
    (ρ : σ → τ) (κ : τ → υ) (hρ : ∀ s, a s = b (ρ s)) (hκ : ∀ t, b t = c (κ t)) :
    (deltaAdjoinDivisionReindex D d b c κ hκ).comp
      (deltaAdjoinDivisionReindex D d a b ρ hρ) =
        deltaAdjoinDivisionReindex D d a c (κ ∘ ρ) (fun s ↦ (hρ s).trans (hκ (ρ s))) := by
  have hf := deltaAdjoinDivisionReindex_spec D d a b ρ hρ
  have hg := deltaAdjoinDivisionReindex_spec D d b c κ hκ
  have hh := deltaAdjoinDivisionReindex_spec D d a c (κ ∘ ρ)
    (fun s ↦ (hρ s).trans (hκ (ρ s)))
  apply deltaAdjoinDivisionHom_ext D (deltaAdjoinDivisionStructure D d c) d a _ _
    (hg.1.comp hf.1) hh.1
  · rw [RingHom.comp_assoc, hf.2.1, hg.2.1, hh.2.1]
  · intro s
    rw [RingHom.comp_apply, hf.2.2, hg.2.2, hh.2.2]
    rfl

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionReindexFunctorial

/-! ## 有限部分族raw包の具体的な有向系 -/

@[expose] public noncomputable section DeltaAdjoinDivisionFiniteSystem

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 元の係数δ環上の有限部分族raw除算包。 -/
abbrev DeltaAdjoinDivisionFiniteStage (T : Finset σ) :=
  DeltaAdjoinDivision D d (fun t : T ↦ a t)

/-- 有限集合包含に沿う標準raw包δ射。 -/
def deltaAdjoinDivisionFiniteMap {S T : Finset σ} (h : S ⊆ T) :
    DeltaAdjoinDivisionFiniteStage D d a S →+* DeltaAdjoinDivisionFiniteStage D d a T :=
  deltaAdjoinDivisionReindex D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun s ↦ ⟨s, h s.property⟩) (fun _ ↦ rfl)

/-- 有限部分族遷移射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionFiniteMap_spec {S T : Finset σ} (h : S ⊆ T) :
    (deltaAdjoinDivisionStructure D d (fun s : S ↦ a s)).IsDeltaHom
        (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
        (deltaAdjoinDivisionFiniteMap D d a h) ∧
      (deltaAdjoinDivisionFiniteMap D d a h).comp
        (deltaAdjoinDivisionMap D d (fun s : S ↦ a s)) =
          deltaAdjoinDivisionMap D d (fun t : T ↦ a t) ∧
      ∀ s : S, deltaAdjoinDivisionFiniteMap D d a h
        (deltaAdjoinDivisionVariable D d (fun s : S ↦ a s) s) =
          deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) ⟨s, h s.property⟩ :=
  deltaAdjoinDivisionReindex_spec D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun s ↦ ⟨s, h s.property⟩) (fun _ ↦ rfl)

/-- 有限部分族の恒等包含はraw包の恒等射。 -/
theorem deltaAdjoinDivisionFiniteMap_self (T : Finset σ) :
    deltaAdjoinDivisionFiniteMap D d a (Finset.Subset.refl T) =
      RingHom.id (DeltaAdjoinDivisionFiniteStage D d a T) :=
  deltaAdjoinDivisionReindex_id D d (fun t : T ↦ a t)

/-- 有限部分族の包含合成はraw包の遷移射の合成を保つ。 -/
theorem deltaAdjoinDivisionFiniteMap_comp {S T U : Finset σ} (h : S ⊆ T) (k : T ⊆ U) :
    (deltaAdjoinDivisionFiniteMap D d a k).comp (deltaAdjoinDivisionFiniteMap D d a h) =
      deltaAdjoinDivisionFiniteMap D d a (h.trans k) :=
  deltaAdjoinDivisionReindex_comp D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun t : U ↦ a t) (fun s ↦ ⟨s, h s.property⟩) (fun t ↦ ⟨t, k t.property⟩)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- 有限部分族raw環のMathlib有向系。 -/
instance deltaAdjoinDivisionFiniteDirectedSystem :
    DirectedSystem (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
      (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) where
  map_self {i} x := by
    rw [deltaAdjoinDivisionFiniteMap_self]
    rfl
  map_map {k j i} hij hjk x :=
    RingHom.congr_fun (deltaAdjoinDivisionFiniteMap_comp D d a hij hjk) x

/-- 有限部分族raw包から全族raw包への標準δ射。 -/
def deltaAdjoinDivisionFiniteToFull (T : Finset σ) :
    DeltaAdjoinDivisionFiniteStage D d a T →+* DeltaAdjoinDivision D d a :=
  deltaAdjoinDivisionReindex D d (fun t : T ↦ a t) a Subtype.val (fun _ ↦ rfl)

/-- 全族への標準射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionFiniteToFull_spec (T : Finset σ) :
    (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).IsDeltaHom
        (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionFiniteToFull D d a T) ∧
      (deltaAdjoinDivisionFiniteToFull D d a T).comp
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t)) = deltaAdjoinDivisionMap D d a ∧
      ∀ t : T, deltaAdjoinDivisionFiniteToFull D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) t) =
          deltaAdjoinDivisionVariable D d a t :=
  deltaAdjoinDivisionReindex_spec D d (fun t : T ↦ a t) a Subtype.val (fun _ ↦ rfl)

/-- 全族への標準射は有限部分族の全遷移射と両立する。 -/
theorem deltaAdjoinDivisionFiniteToFull_compatible {S T : Finset σ} (h : S ⊆ T) :
    (deltaAdjoinDivisionFiniteToFull D d a T).comp (deltaAdjoinDivisionFiniteMap D d a h) =
      deltaAdjoinDivisionFiniteToFull D d a S :=
  deltaAdjoinDivisionReindex_comp D d (fun s : S ↦ a s) (fun t : T ↦ a t) a
    (fun s ↦ ⟨s, h s.property⟩) Subtype.val (fun _ ↦ rfl) (fun _ ↦ rfl)

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionFiniteSystem

/-! ## 有限部分族raw包の環余極限と標準δ構造 -/

@[expose] public noncomputable section DeltaAdjoinDivisionFiniteColimit

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 有限部分族raw包のMathlib環余極限。 -/
abbrev DeltaAdjoinDivisionFiniteColimit :=
  Ring.DirectLimit (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)

/-- 有限部分族から環余極限への標準環射。 -/
def deltaAdjoinDivisionFiniteColimitOf (T : Finset σ) :
    DeltaAdjoinDivisionFiniteStage D d a T →+* DeltaAdjoinDivisionFiniteColimit D d a :=
  Ring.DirectLimit.of _ _ T

/-- 標準段射と有限部分族の遷移射の可換性。 -/
theorem deltaAdjoinDivisionFiniteColimitOf_compatible {S T : Finset σ} (h : S ⊆ T)
    (x : DeltaAdjoinDivisionFiniteStage D d a S) :
    deltaAdjoinDivisionFiniteColimitOf D d a T (deltaAdjoinDivisionFiniteMap D d a h x) =
      deltaAdjoinDivisionFiniteColimitOf D d a S x :=
  Ring.DirectLimit.of_f (G := fun T ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (f := fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) h x

/-- 各段のW₂切断を移した余極限上の環切断。 -/
def deltaAdjoinDivisionFiniteColimitSection :
    DeltaAdjoinDivisionFiniteColimit D d a →+*
      WittTwo p (DeltaAdjoinDivisionFiniteColimit D d a) :=
  deltaDirectLimitSection (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)
    (fun T ↦ deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
    (fun _ _ h ↦ (deltaAdjoinDivisionFiniteMap_spec D d a h).1)

/-- 余極限の切断の各有限段上の公式。 -/
theorem deltaAdjoinDivisionFiniteColimitSection_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitSection D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      wittTwoMap (deltaAdjoinDivisionFiniteColimitOf D d a T)
        ((deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).sectionHom x) :=
  deltaDirectLimitSection_of (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)
    (fun T ↦ deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
    (fun _ _ h ↦ (deltaAdjoinDivisionFiniteMap_spec D d a h).1) T x

/-- 有限部分族環余極限の標準δ構造。 -/
def deltaAdjoinDivisionFiniteColimitStructure :
    DeltaStructure p (DeltaAdjoinDivisionFiniteColimit D d a) :=
  deltaDirectLimitStructure (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)
    (fun T ↦ deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
    (fun _ _ h ↦ (deltaAdjoinDivisionFiniteMap_spec D d a h).1)

/-- 全ての有限段の標準射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitOf_isDeltaHom (T : Finset σ) :
    (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).IsDeltaHom
      (deltaAdjoinDivisionFiniteColimitStructure D d a)
      (deltaAdjoinDivisionFiniteColimitOf D d a T) :=
  deltaDirectLimitOf_isDeltaHom (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)
    (fun T ↦ deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
    (fun _ _ h ↦ (deltaAdjoinDivisionFiniteMap_spec D d a h).1) T

/-- 環余極限から全族raw包への標準環射。 -/
def deltaAdjoinDivisionFiniteColimitToFull :
    DeltaAdjoinDivisionFiniteColimit D d a →+* DeltaAdjoinDivision D d a :=
  Ring.DirectLimit.lift _ _ _ (fun T ↦ deltaAdjoinDivisionFiniteToFull D d a T) (by
    intro S T h x
    exact DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_compatible D d a h) x)

/-- 全族への標準射は各有限段の既存標準射を延長する。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitToFull D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      deltaAdjoinDivisionFiniteToFull D d a T x :=
  Ring.DirectLimit.lift_of _ _ _ T x

/-- 環余極限から全族raw包への標準射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom :
    (deltaAdjoinDivisionFiniteColimitStructure D d a).IsDeltaHom
      (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionFiniteColimitToFull D d a) :=
  deltaDirectLimitLift_isDeltaHom (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)
    (fun T ↦ deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
    (fun _ _ h ↦ (deltaAdjoinDivisionFiniteMap_spec D d a h).1)
    (deltaAdjoinDivisionStructure D d a) (fun T ↦ deltaAdjoinDivisionFiniteToFull D d a T)
    (fun _ _ h x ↦ DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_compatible D d a h) x)
    (fun T ↦ (deltaAdjoinDivisionFiniteToFull_spec D d a T).1)

/-- 空有限段を通る余極限への標準係数射。 -/
def deltaAdjoinDivisionFiniteColimitBaseMap : A →+* DeltaAdjoinDivisionFiniteColimit D d a :=
  (deltaAdjoinDivisionFiniteColimitOf D d a ∅).comp
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t))

/-- 標準係数射は任意の有限段を通る。 -/
theorem deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage (T : Finset σ) (x : A) :
    deltaAdjoinDivisionFiniteColimitBaseMap D d a x =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x) := by
  have h := deltaAdjoinDivisionFiniteColimitOf_compatible D d a (Finset.empty_subset T)
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t) x)
  have hc := DFunLike.congr_fun
    (deltaAdjoinDivisionFiniteMap_spec D d a (Finset.empty_subset T)).2.1 x
  change deltaAdjoinDivisionFiniteMap D d a (Finset.empty_subset T)
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t) x) = _ at hc
  rw [hc] at h
  exact h.symm

/-- 余極限の標準係数射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitBaseMap_isDeltaHom :
    D.IsDeltaHom (deltaAdjoinDivisionFiniteColimitStructure D d a)
      (deltaAdjoinDivisionFiniteColimitBaseMap D d a) :=
  (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a ∅).comp
    (deltaAdjoinDivisionMap_isDeltaHom D d (fun t : (∅ : Finset σ) ↦ a t))

/-- 全族への射と余極限への係数射の合成は全族の標準係数射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_comp_base :
    (deltaAdjoinDivisionFiniteColimitToFull D d a).comp
      (deltaAdjoinDivisionFiniteColimitBaseMap D d a) = deltaAdjoinDivisionMap D d a := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a ∅,
    deltaAdjoinDivisionFiniteColimitToFull_of]
  exact DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_spec D d a ∅).2.1 x

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionFiniteColimit

/-! ## 有限部分族raw環余極限と全族raw包の標準δ同型 -/

@[expose] public noncomputable section DeltaAdjoinDivisionFiniteColimitEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivisionFiniteColimit D d a
local notation "DL" => deltaAdjoinDivisionFiniteColimitStructure D d a
local notation "B" => DeltaAdjoinDivision D d a
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "jL" => deltaAdjoinDivisionFiniteColimitBaseMap D d a
local notation "jB" => deltaAdjoinDivisionMap D d a
local notation "toB" => deltaAdjoinDivisionFiniteColimitToFull D d a

/-- 単元部分族を通る余極限の標準除算変数。 -/
def deltaAdjoinDivisionFiniteColimitVariable (s : σ) : L := by
  classical
  exact deltaAdjoinDivisionFiniteColimitOf D d a {s}
    (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self s⟩)

/-- 余極限変数は、それを含む任意の有限段の変数の像と一致する。 -/
theorem deltaAdjoinDivisionFiniteColimitVariable_eq_stage (T : Finset σ) (s : T) :
    deltaAdjoinDivisionFiniteColimitVariable D d a s =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s) := by
  classical
  have h : ({(s : σ)} : Finset σ) ⊆ T := Finset.singleton_subset_iff.mpr s.property
  have hc := deltaAdjoinDivisionFiniteColimitOf_compatible D d a h
    (deltaAdjoinDivisionVariable D d (fun t : ({(s : σ)} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self _⟩)
  rw [(deltaAdjoinDivisionFiniteMap_spec D d a h).2.2] at hc
  exact hc.symm

/-- 全ての余極限変数は元の除算関係を満たす。 -/
theorem deltaAdjoinDivisionFiniteColimit_relation (s : σ) :
    jL d * deltaAdjoinDivisionFiniteColimitVariable D d a s = jL (a s) := by
  classical
  rw [deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a {s} d,
    deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a {s} (a s)]
  change deltaAdjoinDivisionFiniteColimitOf D d a {s}
      (deltaAdjoinDivisionMap D d (fun t : ({s} : Finset σ) ↦ a t) d) *
    deltaAdjoinDivisionFiniteColimitOf D d a {s}
      (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
        ⟨s, Finset.mem_singleton_self _⟩) = _
  rw [← map_mul, deltaAdjoinDivision_relation]

/-- 全族raw包から有限部分族余極限への標準δ射の普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionFullToFiniteColimit :
    ∃! f : B →+* L, (DB).IsDeltaHom DL f ∧ f.comp jB = jL ∧
      ∀ s, f (deltaAdjoinDivisionVariable D d a s) =
        deltaAdjoinDivisionFiniteColimitVariable D d a s := by
  apply existsUnique_deltaAdjoinDivisionHom D DL d a jL
    (deltaAdjoinDivisionFiniteColimitBaseMap_isDeltaHom D d a)
  exact deltaAdjoinDivisionFiniteColimit_relation D d a

/-- 全族raw包から有限部分族余極限への標準δ射。 -/
def deltaAdjoinDivisionFullToFiniteColimit : B →+* L :=
  (existsUnique_deltaAdjoinDivisionFullToFiniteColimit D d a).choose

/-- 標準逆方向射のδ・係数・変数公式。 -/
theorem deltaAdjoinDivisionFullToFiniteColimit_spec :
    (DB).IsDeltaHom DL (deltaAdjoinDivisionFullToFiniteColimit D d a) ∧
      (deltaAdjoinDivisionFullToFiniteColimit D d a).comp jB = jL ∧
      ∀ s, deltaAdjoinDivisionFullToFiniteColimit D d a
        (deltaAdjoinDivisionVariable D d a s) =
          deltaAdjoinDivisionFiniteColimitVariable D d a s :=
  (existsUnique_deltaAdjoinDivisionFullToFiniteColimit D d a).choose_spec.1

/-- 余極限から全族への射は各標準除算変数を保つ。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_variable (s : σ) :
    toB (deltaAdjoinDivisionFiniteColimitVariable D d a s) =
      deltaAdjoinDivisionVariable D d a s := by
  classical
  change toB (deltaAdjoinDivisionFiniteColimitOf D d a {s}
    (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self _⟩)) = _
  rw [deltaAdjoinDivisionFiniteColimitToFull_of]
  exact (deltaAdjoinDivisionFiniteToFull_spec D d a {s}).2.2 _

/-- 全族raw包上で標準二方向射の合成は恒等射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_comp_inverse :
    (toB).comp (deltaAdjoinDivisionFullToFiniteColimit D d a) = RingHom.id B := by
  have hi := deltaAdjoinDivisionFullToFiniteColimit_spec D d a
  apply deltaAdjoinDivisionHom_ext D DB d a _ _
    ((deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a).comp hi.1) (DB).isDeltaHom_id
  · rw [RingHom.comp_assoc, hi.2.1, deltaAdjoinDivisionFiniteColimitToFull_comp_base,
      RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, hi.2.2, deltaAdjoinDivisionFiniteColimitToFull_variable]
    rfl

/-- 有限部分族余極限上でも標準二方向射の合成は恒等射。 -/
theorem deltaAdjoinDivisionFullToFiniteColimit_comp_inverse :
    (deltaAdjoinDivisionFullToFiniteColimit D d a).comp toB = RingHom.id L := by
  have hi := deltaAdjoinDivisionFullToFiniteColimit_spec D d a
  apply Ring.DirectLimit.hom_ext
  intro T
  apply deltaAdjoinDivisionHom_ext D DL d (fun t : T ↦ a t) _ _
    ((hi.1.comp (deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a)).comp
      (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a T))
    ((DL).isDeltaHom_id.comp (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a T))
  · apply RingHom.ext
    intro x
    change deltaAdjoinDivisionFullToFiniteColimit D d a
      (toB (deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x))) =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x)
    rw [deltaAdjoinDivisionFiniteColimitToFull_of]
    have hc := DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_spec D d a T).2.1 x
    change deltaAdjoinDivisionFiniteToFull D d a T
      (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x) = jB x at hc
    rw [hc]
    have hb := DFunLike.congr_fun hi.2.1 x
    change deltaAdjoinDivisionFullToFiniteColimit D d a (jB x) = jL x at hb
    rw [hb, deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a T]
  · intro s
    change deltaAdjoinDivisionFullToFiniteColimit D d a
      (toB (deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s))) =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s)
    rw [deltaAdjoinDivisionFiniteColimitToFull_of,
      (deltaAdjoinDivisionFiniteToFull_spec D d a T).2.2, hi.2.2,
      deltaAdjoinDivisionFiniteColimitVariable_eq_stage]

/-- 任意族raw包は有限部分族raw環余極限と標準同型。 -/
def deltaAdjoinDivisionFiniteColimitEquiv : L ≃+* B :=
  RingEquiv.ofRingHom toB (deltaAdjoinDivisionFullToFiniteColimit D d a)
    (deltaAdjoinDivisionFiniteColimitToFull_comp_inverse D d a)
    (deltaAdjoinDivisionFullToFiniteColimit_comp_inverse D d a)

/-- 標準余極限同型の両方向はδ構造を保つ。 -/
theorem deltaAdjoinDivisionFiniteColimitEquiv_isDeltaHom :
    (DL).IsDeltaHom DB (deltaAdjoinDivisionFiniteColimitEquiv D d a).toRingHom ∧
      (DB).IsDeltaHom DL (deltaAdjoinDivisionFiniteColimitEquiv D d a).symm.toRingHom :=
  ⟨deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a,
    (deltaAdjoinDivisionFullToFiniteColimit_spec D d a).1⟩

/-- 標準余極限同型は任意有限段の標準射を延長する。 -/
theorem deltaAdjoinDivisionFiniteColimitEquiv_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitEquiv D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      deltaAdjoinDivisionFiniteToFull D d a T x :=
  deltaAdjoinDivisionFiniteColimitToFull_of D d a T x

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionFiniteColimitEquiv
