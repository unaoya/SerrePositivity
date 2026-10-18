module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegreeInclusion
public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeContraction

/-!
概要：KST Def3.1 の係数変更した総外積の同次部分。
方針：同次外積の tensor 包含の像を取り、純粋 tensor で積の次数を示す。
規約：平坦性の仮定を用いず、分裂単射の像として扱う。
使われ方：外積底変更同型の各次数への制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：スカラー拡大した総外積の第n同次部分。
方針：第n外積の tensor 包含の像を取る。
規約：KST Def3.1。使われ方：底変更写像の同次性。 -/
def exteriorTensorDegree (n : ℕ) : Submodule S (S ⊗[R] ExteriorAlgebra R M) :=
  (exteriorBaseChangeDegreeInclusion n).range

/-- 概要：同次元の純粋 tensor は対応する同次部分に入る。
方針：tensor 包含の像の元を直接与える。
規約：KST Def3.1。使われ方：tensor 帰納法の生成元段階。 -/
theorem exteriorTensorDegree_tmul (n : ℕ) (s : S) (z : ExteriorAlgebra R M)
    (hz : z ∈ ExteriorAlgebra.exteriorPower R n M) :
    s ⊗ₜ[R] z ∈ exteriorTensorDegree n :=
  ⟨s ⊗ₜ[R] (⟨z, hz⟩ : ExteriorAlgebra.exteriorPower R n M), rfl⟩

/-- 概要：同次部分の積の次数は和になる。
方針：両因子の tensor 帰納法で元の外積の次数則へ帰着する。
規約：KST Def3.1。使われ方：底変更写像の積による帰納法。 -/
theorem exteriorTensorDegree_mul {n m : ℕ} {x y : S ⊗[R] ExteriorAlgebra R M}
    (hx : x ∈ exteriorTensorDegree n) (hy : y ∈ exteriorTensorDegree m) :
    x * y ∈ exteriorTensorDegree (n + m) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y =>
      change (s ⊗ₜ[R] x.val) * (t ⊗ₜ[R] y.val) ∈ _
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact exteriorTensorDegree_tmul (n + m) (s * t) (x.val * y.val)
        (SetLike.mul_mem_graded x.property y.property)
    | add y z hy hz =>
      rw [map_add, mul_add]
      exact Submodule.add_mem _ hy hz
  | add x z hx hz =>
    rw [map_add, add_mul]
    exact Submodule.add_mem _ hx hz

/-- 概要：係数の像は tensor 外積の次数0に属する。
方針：係数を s⊗1 と表示する。
規約：KST Def3.1。使われ方：同次性の係数段階。 -/
theorem exteriorTensorDegree_algebraMap (s : S) :
    algebraMap S (S ⊗[R] ExteriorAlgebra R M) s ∈ exteriorTensorDegree 0 := by
  change s ⊗ₜ[R] (1 : ExteriorAlgebra R M) ∈ _
  exact exteriorTensorDegree_tmul 0 s 1 (SetLike.one_mem_graded _)

/-- 概要：係数変更後の生成元写像の像は次数1に属する。
方針：tensor 帰納法と元の外積の生成元の次数を使う。
規約：KST Def3.1。使われ方：底変更写像の同次性の生成元段階。 -/
theorem exteriorBaseChangeGenerator_mem (x : S ⊗[R] M) :
    exteriorBaseChangeGenerator x ∈ exteriorTensorDegree 1 := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    apply exteriorTensorDegree_tmul 1 s (ExteriorAlgebra.ι R m)
    simp only [ExteriorAlgebra.exteriorPower, pow_one]
    exact LinearMap.mem_range_self _ _
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- 概要：外積の順基底変更写像は同次次数を保つ。
方針：同次外積の係数・和・生成元積による帰納法を使う。
規約：KST Def3.1、平坦性不要。使われ方：次数別底変更写像の構成。 -/
theorem exteriorToBaseChange_mem_degree (n : ℕ)
    (z : ExteriorAlgebra S (S ⊗[R] M))
    (hz : z ∈ ExteriorAlgebra.exteriorPower S n (S ⊗[R] M)) :
    exteriorToBaseChange z ∈ exteriorTensorDegree n := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [AlgHom.commutes]
    exact exteriorTensorDegree_algebraMap s
  | add _ _ _ _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | mem_mul _ hx _ _ _ hy =>
    obtain ⟨x, rfl⟩ := hx
    rw [map_mul, exteriorToBaseChange_ι_all]
    simpa only [Nat.one_add] using
      exteriorTensorDegree_mul (exteriorBaseChangeGenerator_mem x) hy

end SerrePositivity.KST.DerivedBlowup
