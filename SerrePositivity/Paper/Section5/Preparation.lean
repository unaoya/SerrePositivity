module

public import SerrePositivity.Paper.Section2.TowerApproximation
public import SerrePositivity.IntersectionMultiplicity.ParameterQuotientTor
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic

/-!
# §5.2 の準備：(5.6) の冪と `S` の `U` への作用 `θ`

## 概要

論文 §5.2–5.3 で Lemma 5.4（`Section5.lemma_5_4`）を適用するための対象を作る。

- **(5.6)**（`exists_pow_maximalIdeal_map_le`）：局所準同型 `f : B → D′`（`D′` は Noether 局所）と
  `m_{D′}` 準素なイデアル `I` について、`a ≥ 1` で `f(m_B^a) ⊆ I`。論文では `B = R/(x)`、
  `I = I_σ` で、`m_B^a` は `D′/I_σ` と `U` を消す。
- **θ の構成**（`paramTheta`）：`ι : R → D′`（論文の `ι_σ`）、`D′ → C`、`Λ → C` が `A` 上で両立する
  とき、`T = D′/I_σ`（`I_σ = (ι(x))D′`）、`U = C/(x)C`（`R` は `ι` を通して `C` に作用）として
  `θ : S = Λ ⊗_A T → U`、`λ ⊗ t ↦ λ · t`。`Λ` の作用と `B` の作用に両立する
  （`paramTheta_comp_tower`、`paramTheta_comp_ψU`）。これは Lemma 5.4 の仮定 `hθΛ`、`hθB` である。

## 規約

`φσ ι = (D′ → C) ∘ ι` を `R` の `C` への作用とする（`ParamQuot.U`、`ParamQuot.ψ` はこの `φ` で使う）。
`B → T` は `ι` の誘導する `R/(x) → D′/I_σ`（`paramBT`）。
-/

@[expose] public section

universe u

namespace SerrePositivity

open IsLocalRing ParamQuot

namespace Section5

/-! ## (5.6) -/

/-! ## `θ : Λ ⊗_A (D′/I_σ) → C/(x)C` -/

section theta

variable {R D C : Type u} [CommRing R] [CommRing D] [CommRing C] [Algebra D C] (ι : R →+* D)
  {h : ℕ} (x : Fin h → R)

/-- `R` の `C` への作用 `(D′ → C) ∘ ι`。 -/
noncomputable abbrev φσ : R →+* C := (algebraMap D C).comp ι

/-- `I_σ = (ι(x_1), …, ι(x_h)) D′`。 -/
abbrev Iσ : Ideal D := Ideal.span (Set.range (ι ∘ x))

/-- `T = D′/I_σ`。 -/
abbrev TD : Type u := D ⧸ Iσ ι x

lemma Iσ_le_comap : Iσ ι x ≤ (IC (φσ (C := C) ι) x).comap (algebraMap D C) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

lemma span_le_comap_Iσ : Ideal.span (Set.range x) ≤ (Iσ ι x).comap ι := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.subset_span ⟨i, rfl⟩

/-- `B = R/(x) → T = D′/I_σ`（`ι` の誘導）。 -/
noncomputable def paramBT : B x →+* TD ι x :=
  Ideal.quotientMap (Iσ ι x) ι (span_le_comap_Iσ ι x)

/-- `T = D′/I_σ → U = C/(x)C`。 -/
noncomputable def paramTU : TD ι x →+* U (φσ (C := C) ι) x :=
  Ideal.quotientMap _ (algebraMap D C) (Iσ_le_comap ι x)

variable (A : Type u) [CommRing A] {hA : ℕ} (t : Fin hA → A) (p : ℕ) [Algebra A D]
  [Algebra (Section2.Tower A t p) C]

/-- **θ**：`Λ → C` と `D′ → C` が `A` 上で両立する（`hAC`）とき、`S = Λ ⊗_A (D′/I_σ) → U = C/(x)C`、
`λ ⊗ t ↦ λ · t`。 -/
noncomputable def paramTheta
    (hAC : (algebraMap (Section2.Tower A t p) C).comp (algebraMap A (Section2.Tower A t p)) =
      (algebraMap D C).comp (algebraMap A D)) :
    Section2.TS A t p (TD ι x) →+* U (φσ (C := C) ι) x :=
  letI : Algebra A (U (φσ (C := C) ι) x) :=
    ((Ideal.Quotient.mk _).comp ((algebraMap (Section2.Tower A t p) C).comp
      (algebraMap A (Section2.Tower A t p)))).toAlgebra
  (Algebra.TensorProduct.lift (S := A)
    { toRingHom := (Ideal.Quotient.mk (IC (φσ (C := C) ι) x)).comp
        (algebraMap (Section2.Tower A t p) C)
      commutes' := fun _ ↦ rfl }
    { toRingHom := paramTU ι x
      commutes' := fun a ↦ by
        change Ideal.Quotient.mk _ (algebraMap D C (algebraMap A D a)) =
          Ideal.Quotient.mk _ (((algebraMap (Section2.Tower A t p) C).comp
            (algebraMap A (Section2.Tower A t p))) a)
        rw [hAC]
        rfl }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

variable {A t p}

/-- `θ` は `Λ` の作用と両立（Lemma 5.4 の `hθΛ`）。 -/
theorem paramTheta_comp_tower
    (hAC : (algebraMap (Section2.Tower A t p) C).comp (algebraMap A (Section2.Tower A t p)) =
      (algebraMap D C).comp (algebraMap A D)) :
    (paramTheta ι x A t p hAC).comp
        (algebraMap (Section2.Tower A t p) (Section2.TS A t p (TD ι x))) =
      (Ideal.Quotient.mk (IC (φσ (C := C) ι) x)).comp (algebraMap (Section2.Tower A t p) C) := by
  refine RingHom.ext fun l ↦ ?_
  change paramTheta ι x A t p hAC (l ⊗ₜ 1) = _
  simp only [paramTheta, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- `θ` は `B` の作用と両立（Lemma 5.4 の `hθB`）。`B → T` は `paramBT`。 -/
theorem paramTheta_comp_ψU
    (hAC : (algebraMap (Section2.Tower A t p) C).comp (algebraMap A (Section2.Tower A t p)) =
      (algebraMap D C).comp (algebraMap A D))
    [Algebra (B x) (TD ι x)] (hBT : algebraMap (B x) (TD ι x) = paramBT ι x) :
    (paramTheta ι x A t p hAC).comp (Section2.ψU A t p (TD ι x) (B x)) =
      ψ (φσ (C := C) ι) x := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  change paramTheta ι x A t p hAC (1 ⊗ₜ algebraMap (B x) (TD ι x) (Ideal.Quotient.mk _ r)) = _
  simp only [paramTheta, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul, hBT]
  rfl

end theta

end Section5

end SerrePositivity
