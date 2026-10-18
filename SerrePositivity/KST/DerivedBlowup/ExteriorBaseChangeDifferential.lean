module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChange

/-!
概要：KST Def3.1 の Koszul 生成元微分と収縮のスカラー拡大。
方針：微分の線形写像を tensor し、基底環の単位同型で係数環へ戻す。
規約：任意の可換環の代数、2の可逆性不要。
使われ方：外積代数の基底変更同型の微分適合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：Koszul 生成元微分のスカラー拡大。
方針：S⊗d の後に S⊗R≃S を合成する。
規約：KST Def3.1。使われ方：係数変更後の外積 Koszul 微分。 -/
def exteriorBaseChangeDifferential (d : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) d)

/-- 概要：スカラー拡大した生成元微分の純粋 tensor 上の値。
方針：右単位同型を評価し、係数の積の順序を整理する。
規約：KST Def3.1。使われ方：基底変更後の Leibniz 公式。 -/
@[simp] theorem exteriorBaseChangeDifferential_tmul (d : M →ₗ[R] R) (s : S) (m : M) :
    exteriorBaseChangeDifferential d (s ⊗ₜ[R] m) = s * algebraMap R S (d m) := by
  change d m • s = _
  rw [Algebra.smul_def, mul_comm]

/-- 概要：元の外積収縮の項別スカラー拡大。
方針：S 側の恒等写像と元の収縮を tensor する。
規約：KST Def3.1。使われ方：基底変更前後の微分の比較対象。 -/
def exteriorBaseChangeContraction (d : M →ₗ[R] R) :
    S ⊗[R] ExteriorAlgebra R M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
    (CliffordAlgebra.contractLeft (Q := 0) d)

/-- 概要：スカラー拡大した収縮の純粋 tensor 上の値。
方針：tensor 線形写像を評価する。
規約：KST Def3.1。使われ方：微分適合性の tensor 帰納法。 -/
@[simp] theorem exteriorBaseChangeContraction_tmul (d : M →ₗ[R] R) (s : S)
    (z : ExteriorAlgebra R M) :
    exteriorBaseChangeContraction d (s ⊗ₜ[R] z) =
      s ⊗ₜ[R] CliffordAlgebra.contractLeft (Q := 0) d z := rfl

/-- 概要：純粋な係数変更生成元による左乗法に対する収縮の公式。
方針：第二因子の tensor 帰納法で元の contractLeft_ι_mul に帰着する。
規約：KST Def3.1。使われ方：基底変更同型と収縮の可換性。 -/
theorem exteriorBaseChangeContraction_generator_mul (d : M →ₗ[R] R) (s : S) (m : M)
    (z : S ⊗[R] ExteriorAlgebra R M) :
    exteriorBaseChangeContraction d ((s ⊗ₜ[R] ExteriorAlgebra.ι R m) * z) =
      (s * algebraMap R S (d m)) • z -
        (s ⊗ₜ[R] ExteriorAlgebra.ι R m) * exteriorBaseChangeContraction d z := by
  induction z using TensorProduct.inductionOn with
  | tmul t z =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, exteriorBaseChangeContraction_tmul,
      CliffordAlgebra.contractLeft_ι_mul, TensorProduct.tmul_sub,
      exteriorBaseChangeContraction_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    rw [TensorProduct.tmul_smul]
    simp only [TensorProduct.smul_tmul']
    simp only [Algebra.smul_def]
    congr 1
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | add x y hx hy =>
    simp only [mul_add, map_add, smul_add, hx, hy]
    abel

end SerrePositivity.KST.DerivedBlowup
