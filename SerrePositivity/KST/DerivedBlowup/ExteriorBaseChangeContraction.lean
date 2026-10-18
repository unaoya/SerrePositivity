module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDifferential

/-!
概要：KST Def3.1 の外積代数の基底変更同型は収縮微分と可換。
方針：生成元に対する Leibniz 公式を tensor 帰納法で延長し、外積の左帰納法を使う。
規約：任意可換環上で2の可逆性を使わない。
使われ方：Koszul dg 代数の基底変更比較の微分適合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：基底変更後の任意の生成元の像。
方針：外積の普遍写像の生成元公式を使う。
規約：KST Def3.1。使われ方：収縮微分の自然性。 -/
theorem exteriorToBaseChange_ι_all (x : S ⊗[R] M) :
    exteriorToBaseChange (ExteriorAlgebra.ι S x) = exteriorBaseChangeGenerator x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

/-- 概要：任意の基底変更生成元との積に対する収縮の Leibniz 公式。
方針：純粋生成元の公式を tensor の加法的生成で延長する。
規約：KST Def3.1。使われ方：外積上の帰納法の生成元段階。 -/
theorem exteriorBaseChangeContraction_mul (d : M →ₗ[R] R) (x : S ⊗[R] M)
    (z : S ⊗[R] ExteriorAlgebra R M) :
    exteriorBaseChangeContraction d (exteriorBaseChangeGenerator x * z) =
      exteriorBaseChangeDifferential d x • z -
        exteriorBaseChangeGenerator x * exteriorBaseChangeContraction d z := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [exteriorBaseChangeDifferential_tmul]
    exact exteriorBaseChangeContraction_generator_mul d s m z
  | add x y hx hy =>
    simp only [map_add, add_mul, add_smul, hx, hy]
    abel

/-- 概要：外積の基底変更射は Koszul 収縮と可換。
方針：係数・和・生成元による左乗法で帰納し、生成元の Leibniz 公式を使う。
規約：KST Def3.1。使われ方：dg 代数としての底変更比較。 -/
theorem exteriorToBaseChange_contract (d : M →ₗ[R] R)
    (z : ExteriorAlgebra S (S ⊗[R] M)) :
    exteriorBaseChangeContraction d (exteriorToBaseChange z) =
      exteriorToBaseChange
        (CliffordAlgebra.contractLeft (Q := 0) (exteriorBaseChangeDifferential d) z) := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap s =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
    change exteriorBaseChangeContraction d (s ⊗ₜ[R] 1) = 0
    rw [exteriorBaseChangeContraction_tmul]
    simp [CliffordAlgebra.contractLeft_one]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul z x hz =>
    rw [map_mul, exteriorToBaseChange_ι_all, exteriorBaseChangeContraction_mul,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      exteriorToBaseChange_ι_all, hz]

/-- 概要：基底変更射の逆射も Koszul 収縮と可換。
方針：順写像の単射性で比較し、順写像の微分適合性と逆元律を使う。
規約：KST Def3.1。使われ方：基底変更の dg 同型の逆射。 -/
theorem exteriorOfBaseChange_contract (d : M →ₗ[R] R)
    (z : S ⊗[R] ExteriorAlgebra R M) :
    exteriorOfBaseChange (exteriorBaseChangeContraction d z) =
      CliffordAlgebra.contractLeft (Q := 0) (exteriorBaseChangeDifferential d)
        (exteriorOfBaseChange z) := by
  apply (exteriorBaseChangeEquiv (R := R) (S := S) (M := M)).injective
  change exteriorToBaseChange (exteriorOfBaseChange (exteriorBaseChangeContraction d z)) =
    exteriorToBaseChange
      (CliffordAlgebra.contractLeft (Q := 0) (exteriorBaseChangeDifferential d)
        (exteriorOfBaseChange z))
  rw [← exteriorToBaseChange_contract]
  have h (w : S ⊗[R] ExteriorAlgebra R M) :
      exteriorToBaseChange (exteriorOfBaseChange w) = w :=
    AlgHom.congr_fun exteriorToBaseChange_comp_of w
  rw [h, h]

end SerrePositivity.KST.DerivedBlowup
