module

public import SerrePositivity.CLMST.StageFiniteness
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # 有限段の基底変更の単射性と次元

根の塔の単項式基底を D へ基底変更し、D_n=A_n⊗_A D の D 上の基底を得る。
D が非零なら基底から D_n も非零であり、自由性から標準写像 D→D_n は単射。
有限性から整性を得て、単射な整拡大の次元保存を適用する。
Noether 性、局所性、基底 A→D の単射性や有限性は必要ない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 有限段の基底変更の D 上の単項式基底。基底の添字は根の各指数を記録する。 -/
def stageAlgebraBasis (n : ℕ) :
    Module.Basis (Fin h → Fin (p ^ n)) D (StageAlgebra A D t p n) := by
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (D ⊗[A] TowerStage A t p n) ≃ₐ[D] StageAlgebra A D t p n :=
    Algebra.TensorProduct.commRight A D (TowerStage A t p n)
  exact ((towerStageBasis A t p n).baseChange D).map e.toLinearEquiv

/-- 各有限段は D 上自由。D が A 上有限であるという仮定は不要。 -/
theorem stageAlgebra_free (n : ℕ) : Module.Free D (StageAlgebra A D t p n) :=
  Module.Free.of_basis (stageAlgebraBasis A D t p n)

/-- D 上の有限段のランクは、長さの正規化係数と同じ p^(nh)。 -/
theorem finrank_stageAlgebra [Nontrivial D] (n : ℕ) :
    Module.finrank D (StageAlgebra A D t p n) = stageRank h p n := by
  rw [Module.finrank_eq_card_basis (stageAlgebraBasis A D t p n),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, stageRank, pow_mul]

/-- D が非零なら、各有限段も非零。非空の単項式基底の元を使う。 -/
theorem stageAlgebra_nontrivial [Nontrivial D] (n : ℕ) :
    Nontrivial (StageAlgebra A D t p n) :=
  nontrivial_of_ne _ _ ((stageAlgebraBasis A D t p n).ne_zero
    (fun _ ↦ ⟨0, pow_pos_of_prime p n⟩))

/-- D から有限段への標準代数写像は単射。自由性と非零性から忠実な作用を得る。 -/
theorem stageAlgebra_algebraMap_injective [Nontrivial D] (n : ℕ) :
    Function.Injective (algebraMap D (StageAlgebra A D t p n)) := by
  let := stageAlgebra_free A D t p n
  let := stageAlgebra_nontrivial A D t p n
  exact FaithfulSMul.algebraMap_injective D (StageAlgebra A D t p n)

/-- 有限段の基底変更は D と同じ Krull 次元を持つ。有限単射整拡大の次元保存による。 -/
theorem ringKrullDim_stageAlgebra [Nontrivial D] (n : ℕ) :
    ringKrullDim (StageAlgebra A D t p n) = ringKrullDim D :=
  ringKrullDim_eq_of_integral_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)

end SerrePositivity.CLMST
