module

public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-! # 剰余体の基底を持ち上げた極小自由被覆

有限生成加群 `M` に対し、`k ⊗ M` の基底を持ち上げて `R^b → M` を作る。
Nakayama による全射性と、核の全座標が極大イデアルに入ることを証明する。
環の正則性・Noether 性はこの一段の構成には必要ない。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.MinimalGenerators

open CategoryTheory IsLocalRing TensorProduct

variable {R : Type u} [CommRing R] [IsLocalRing R] (M : FGModuleCat.{u} R)

/-- 剰余体で測った極小生成元数。 -/
noncomputable def rank : ℕ := Module.finrank (ResidueField R) (ResidueField R ⊗[R] M)

/-- 剰余体への係数変更で選んだ有限基底。 -/
noncomputable def basis : Module.Basis (Fin (rank M)) (ResidueField R) (ResidueField R ⊗[R] M) :=
  Module.finBasis (ResidueField R) (ResidueField R ⊗[R] M)

/-- 剰余体上の基底の持ち上げ。 -/
noncomputable def generator (i : Fin (rank M)) : M :=
  (TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective (basis M i)).choose

lemma generator_tmul (i : Fin (rank M)) :
    (1 : ResidueField R) ⊗ₜ[R] generator M i = basis M i :=
  (TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective
    (basis M i)).choose_spec

/-- 極小生成元を基底とする標準有限自由加群。 -/
def cover : ModuleCat.{u} R := ModuleCat.of R (Fin (rank M) → R)

instance cover_free : Module.Free R (cover M) := by
  unfold cover
  infer_instance

instance cover_finite : Module.Finite R (cover M) := by
  unfold cover
  infer_instance

/-- 基底の持ち上げによる自由被覆の射。 -/
noncomputable def π : cover M →ₗ[R] M :=
  ∑ i, (LinearMap.toSpanSingleton R M (generator M i)).comp (LinearMap.proj i)

lemma π_apply (a : cover M) : π M a = ∑ i, a i • generator M i := by
  simp only [π, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  rfl

lemma π_surjective : Function.Surjective (π M) := by
  classical
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis (generator M) (basis M) (generator_tmul M)
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simp [π_apply]⟩

/-- 剰余体での被覆の射は、選んだ基底による線形結合になる。 -/
lemma π_tmul (a : cover M) :
    (1 : ResidueField R) ⊗ₜ[R] π M a =
      ∑ i, residue R (a i) • basis M i := by
  rw [π_apply, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← generator_tmul M i, TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rfl

/-- 極小被覆の核の各座標は極大イデアルに入る。 -/
lemma ker_coordinate_mem {a : cover M} (ha : π M a = 0) (i : Fin (rank M)) :
    a i ∈ maximalIdeal R := by
  classical
  apply (residue_eq_zero_iff _).mp
  have hsum : ∑ j, residue R (a j) • basis M j = 0 := by
    rw [← π_tmul, ha, TensorProduct.tmul_zero]
  have hcoeff := congrArg (fun y ↦ (basis M).repr y i) hsum
  simpa [Finsupp.single_apply] using hcoeff

/-- 零次 Tor の長さは、この被覆の階数に一致する。 -/
lemma length_tor_zero :
    Module.length R (TorModule R 0 M (R ⧸ maximalIdeal R)) = rank M := by
  rw [((torModuleZeroEquiv R M (R ⧸ maximalIdeal R)).trans
    (TensorProduct.comm R M (R ⧸ maximalIdeal R))).length_eq]
  change Module.length R (ResidueField R ⊗[R] M) = _
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField R)
    Ideal.Quotient.mk_surjective, Module.length_eq_finrank]
  rfl

/-- 極小被覆を剰余体へ移した次元は、元の加群の極小生成元数である。 -/
lemma rank_cover : rank (FGModuleCat.of R (cover M)) = rank M := by
  unfold rank
  rw [Module.finrank_baseChange]
  change Module.finrank R (Fin (rank M) → R) = _
  simp [rank]

end SerrePositivity.MinimalGenerators
