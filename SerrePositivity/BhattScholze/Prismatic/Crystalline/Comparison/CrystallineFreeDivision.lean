module

public import SerrePositivity.BhattScholze.Delta.Division.Basic

/-!
# 自由 δ 環での差の p 除算

## 概要
自由変数のうち第二族と第一族の指定変数との差を p で割って添加すると、再び自由 δ 環になる。

## 方針
第二族の変数を、第一族の指定変数と p 倍した新変数の和に取り替える。

## 規約
完備化前の δ 環を扱う。

## 使われ方
結晶比較における Čech–Alexander の源と Frobenius 底変換。
-/

public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S T : Type v}
    (D : DeltaStructure p R) (b : T → S)

local notation "A" => RelativeFreeDeltaRing (R := R) (S ⊕ T)
local notation "E" => relativeFreeDeltaStructure (S ⊕ T) D

private abbrev x (i : S ⊕ T) : A := MvPolynomial.X (i, 0)

/-- 第一族の指定座標を基点とした第二族の差。 -/
abbrev crystallineFreeDivisionDifference (t : T) : A :=
  MvPolynomial.X (Sum.inr t, 0) - MvPolynomial.X (Sum.inl (b t), 0)

local notation "B" => DeltaAdjoinDivision E (p : A) (crystallineFreeDivisionDifference b)
local notation "F" => deltaAdjoinDivisionStructure E (p : A) (crystallineFreeDivisionDifference b)
local notation "j" => deltaAdjoinDivisionMap E (p : A) (crystallineFreeDivisionDifference b)
local notation "v" => deltaAdjoinDivisionVariable E (p : A) (crystallineFreeDivisionDifference b)
local notation "C" => (MvPolynomial.C : R →+* A)

private def replace : A →+* A :=
  relativeFreeDeltaEval E C
    (Sum.elim (fun s => x (Sum.inl s)) (fun t => (p : A) * x (Sum.inr t) + x (Sum.inl (b t))))

private theorem replace_isDeltaHom : DeltaStructure.IsDeltaHom E E (replace D b) :=
  relativeFreeDeltaEval_isDeltaHom D E C (relativeFreeDeltaStructure_C_isDeltaHom _ D) _

private theorem replace_x_inl (s : S) : replace D b (x (Sum.inl s)) = x (Sum.inl s) := by
  simp [replace]

private theorem replace_x_inr (t : T) :
    replace D b (x (Sum.inr t)) = (p : A) * x (Sum.inr t) + x (Sum.inl (b t)) := by
  simp [replace]

private theorem forward_exists : ∃! h : B →+* A,
    DeltaStructure.IsDeltaHom F E h ∧ h.comp j = replace D b ∧ ∀ t, h (v t) = x (Sum.inr t) := by
  apply existsUnique_deltaAdjoinDivisionHom E E (p : A) (crystallineFreeDivisionDifference b)
    (replace D b) (replace_isDeltaHom D b)
  intro t
  rw [map_natCast, map_sub, replace_x_inr, replace_x_inl, add_sub_cancel_right]

private def forward : B →+* A := (forward_exists D b).choose

private theorem forward_spec :
    DeltaStructure.IsDeltaHom F E (forward D b) ∧ (forward D b).comp j = replace D b ∧
      ∀ t, forward D b (v t) = x (Sum.inr t) :=
  (forward_exists D b).choose_spec.1

private def backward : A →+* B :=
  relativeFreeDeltaEval F ((j).comp C)
    (Sum.elim (fun s => j (x (Sum.inl s))) (fun t => v t))

private theorem backward_isDeltaHom : DeltaStructure.IsDeltaHom E F (backward D b) :=
  relativeFreeDeltaEval_isDeltaHom D F ((j).comp C)
    ((deltaAdjoinDivisionMap_isDeltaHom E (p : A) (crystallineFreeDivisionDifference b)).comp
      (relativeFreeDeltaStructure_C_isDeltaHom _ D)) _

private theorem backward_x_inl (s : S) : backward D b (x (Sum.inl s)) = j (x (Sum.inl s)) := by
  simp [backward]

private theorem backward_x_inr (t : T) : backward D b (x (Sum.inr t)) = v t := by
  simp [backward]

private theorem eq_of_initial {U : Type*} [CommRing U] (G : DeltaStructure p U) (f g : A →+* U)
    (hf : DeltaStructure.IsDeltaHom E G f) (hg : DeltaStructure.IsDeltaHom E G g)
    (hC : f.comp C = g.comp C) (hX : ∀ i : S ⊕ T, f (x i) = g (x i)) : f = g := by
  apply MvPolynomial.ringHom_ext' hC
  rintro ⟨s, n⟩
  rw [relativeFreeDeltaHom_X_iterates D G f hf, relativeFreeDeltaHom_X_iterates D G g hg,
    hX s]

private theorem forward_comp_backward : (forward D b).comp (backward D b) = RingHom.id A := by
  obtain ⟨hd, hc, hv⟩ := forward_spec D b
  apply eq_of_initial D E _ _ (hd.comp (backward_isDeltaHom D b)) (fun _ => rfl)
  · apply RingHom.ext
    intro r
    change forward D b (backward D b (MvPolynomial.C r)) = MvPolynomial.C r
    rw [backward, relativeFreeDeltaEval_C]
    exact (DFunLike.congr_fun hc (MvPolynomial.C r)).trans
      (relativeFreeDeltaEval_C _ _ _ r)
  · intro i
    cases i with
    | inl s =>
      change forward D b (backward D b (x (Sum.inl s))) = x (Sum.inl s)
      rw [backward_x_inl]
      exact (DFunLike.congr_fun hc _).trans (replace_x_inl D b s)
    | inr t =>
      change forward D b (backward D b (x (Sum.inr t))) = x (Sum.inr t)
      rw [backward_x_inr, hv]

private theorem backward_comp_replace : (backward D b).comp (replace D b) = j := by
  apply eq_of_initial D F _ _ ((backward_isDeltaHom D b).comp (replace_isDeltaHom D b))
    (deltaAdjoinDivisionMap_isDeltaHom E (p : A) (crystallineFreeDivisionDifference b))
  · apply RingHom.ext
    intro r
    change backward D b (replace D b (MvPolynomial.C r)) = j (MvPolynomial.C r)
    rw [replace, relativeFreeDeltaEval_C, backward, relativeFreeDeltaEval_C]
    rfl
  · intro i
    cases i with
    | inl s =>
      change backward D b (replace D b (x (Sum.inl s))) = j (x (Sum.inl s))
      rw [replace_x_inl, backward_x_inl]
    | inr t =>
      change backward D b (replace D b (x (Sum.inr t))) = j (x (Sum.inr t))
      rw [replace_x_inr, map_add, map_mul, map_natCast, backward_x_inl, backward_x_inr,
        ← map_natCast j p, deltaAdjoinDivision_relation]
      rw [map_sub, sub_add_cancel]

private theorem backward_comp_forward : (backward D b).comp (forward D b) = RingHom.id B := by
  obtain ⟨hd, hc, hv⟩ := forward_spec D b
  obtain ⟨g, _, hu⟩ := existsUnique_deltaAdjoinDivisionHom E F (p : A) (crystallineFreeDivisionDifference b) j
    (deltaAdjoinDivisionMap_isDeltaHom E (p : A) (crystallineFreeDivisionDifference b)) v
    (deltaAdjoinDivision_relation E (p : A) (crystallineFreeDivisionDifference b))
  have h₁ := hu ((backward D b).comp (forward D b)) ⟨(backward_isDeltaHom D b).comp hd,
    by rw [RingHom.comp_assoc, hc, backward_comp_replace], fun t => by
      change backward D b (forward D b (v t)) = v t
      rw [hv, backward_x_inr]⟩
  have h₂ := hu (RingHom.id B) ⟨fun _ => rfl, RingHom.id_comp _, fun _ => rfl⟩
  exact h₁.trans h₂.symm

set_option maxHeartbeats 400000 in
/-- 差の p 除算を添加した環は、新しい変数の自由 δ 環と同型。 -/
def crystallineFreeDivisionEquiv : B ≃+* A :=
  RingEquiv.ofRingHom (forward D b) (backward D b)
    (forward_comp_backward D b) (backward_comp_forward D b)

end SerrePositivity.BhattScholze.Prismatic
