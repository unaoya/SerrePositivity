module

public import SerrePositivity.Asymptotic.SequenceKoszul
public import SerrePositivity.CategoryTheory.ScalarZeroCone
public import SerrePositivity.CategoryTheory.ScalarSupportLocalization

/-! # Koszul 複体列の一様な台と、商で零となるスカラー作用 -/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 係数複体の台によらず、Koszul 複体列は一様に支持される。 -/
lemma sequenceKoszul_supported {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    scalarSupported x (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK)) := by
  induction n with
  | zero => exact ⟨1, by omega, fun j ↦ j.elim0⟩
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let a := x (Fin.last n)
      let T := sequenceConeTriangle (a • 𝟙 P) hP hP
      have hT := sequenceConeTriangle_distinguished (a • 𝟙 P) hP hP
      have hi := scalarSupported_triangle (Fin.init x) T hT (ih _) (ih _)
      have ha : (a * a) • 𝟙 T.obj₃ = 0 :=
        smul_mul_self_id_eq_zero T hT a
          (by
            change (a • 𝟙 (sequenceHomotopyObj P hP)) ≫ T.mor₂ = 0
            rw [← sequenceConeTriangle_smul_mor₁ a P hP]
            exact comp_distTriang_mor_zero₁₂ T hT)
          (by
            change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map
              (a • 𝟙 (sequenceHomotopyObj P hP)) = 0
            rw [← sequenceConeTriangle_smul_mor₁ a P hP]
            exact comp_distTriang_mor_zero₃₁ T hT)
      exact scalarSupported_fin_succ x T.obj₃ hi 2 (by omega) (by simpa only [pow_two] using ha)

/-- 共通の正の冪で作った Koszul 複体も元のパラメータ系で一様に支持される。 -/
lemma sequenceKoszul_pow_supported {n : ℕ} (x : Fin n → R) (v : ℕ) (hv : 0 < v)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    scalarSupported x (sequenceHomotopyObj (sequenceKoszul (fun j ↦ x j ^ v) K)
      (sequenceKoszul_bounded _ K hK)) := by
  obtain ⟨w, hw, h⟩ := sequenceKoszul_supported (fun j ↦ x j ^ v) K hK
  exact ⟨v * w, Nat.mul_pos hv hw, fun j ↦ by simpa only [pow_mul] using h j⟩

variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  (F : SequenceHomotopy R s ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

omit [F.Linear R] in
/-- Koszul の反復は、像で既に成り立つ支持条件を保つ。 -/
lemma sequenceKoszul_map_supported {e n : ℕ} (z : Fin e → R) (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (F.obj (sequenceHomotopyObj K hK))) :
    scalarSupported z (F.obj (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK))) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let T := sequenceConeTriangle (x (Fin.last n) • 𝟙 P) hP hP
      exact scalarSupported_triangle z (F.mapTriangle.obj T)
        (F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)) (ih _) (ih _)

/-- パラメータが像で零なら、反復する錐は元の消去スカラーをそのまま保つ。 -/
lemma sequenceKoszul_map_smul_zero {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hx : ∀ j, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0)
    (a : R) (ha : a • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0) :
    a • 𝟙 (F.obj (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK))) = 0 := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let c := x (Fin.last n)
      let T := sequenceConeTriangle (c • 𝟙 P) hP hP
      have hT := F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)
      have hc := ih (Fin.init x) (fun j ↦ hx j.castSucc) c (hx (Fin.last n))
      have ha' := ih (Fin.init x) (fun j ↦ hx j.castSucc) a ha
      have hf : (F.mapTriangle.obj T).mor₁ = 0 := by
        change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
          (sequenceConeTriangle (c • 𝟙 P) hP hP).mor₁) = 0
        rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
        exact hc
      exact scalar_zero_on_zero_cone (F.mapTriangle.obj T) hT hf a ha' ha'

end SerrePositivity.Asymptotic
