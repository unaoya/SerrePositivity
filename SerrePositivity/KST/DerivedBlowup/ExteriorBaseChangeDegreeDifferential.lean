module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegree

/-!
概要：KST Def3.1 の同次外積の基底変更は次数別 Koszul 微分と可換。
方針：分裂単射である tensor 同次包含を通して総外積の微分比較へ帰着する。
規約：基底環と係数環は任意可換環。
使われ方：整数次数 Koszul 複体の底変更同型の chain 条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：次数別の順基底変更を総外積へ含めると総基底変更になる。
方針：同次射影と包含の逆元律を使う。
規約：KST Def3.1。使われ方：微分と乗法の同次比較。 -/
theorem exteriorDegreeToBaseChange_inclusion (n : ℕ)
    (z : ExteriorAlgebra.exteriorPower S n (S ⊗[R] M)) :
    exteriorBaseChangeDegreeInclusion n (exteriorDegreeToBaseChange n z) =
      exteriorToBaseChange z.val :=
  exteriorBaseChangeDegreeInclusion_projection n _
    (exteriorToBaseChange_mem_degree n z.val z.property)

/-- 概要：次数別収縮の tensor は総収縮の tensor と整合する。
方針：純粋 tensor で評価し、加法的に延長する。
規約：KST Def3.1。使われ方：底変更後の微分の同次包含。 -/
theorem exteriorBaseChangeDegreeInclusion_d (d : M →ₗ[R] R) (n : ℕ)
    (z : S ⊗[R] ExteriorAlgebra.exteriorPower R (n + 1) M) :
    exteriorBaseChangeDegreeInclusion n
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
          (exteriorDegreeDifferential d n) z) =
      exteriorBaseChangeContraction d (exteriorBaseChangeDegreeInclusion (n + 1) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：同次外積の基底変更同型は Koszul 微分と可換。
方針：tensor 同次包含の単射性と総収縮の基底変更適合性を使う。
規約：KST Def3.1。使われ方：Koszul chain 複体の底変更同型。 -/
theorem exteriorDegreeToBaseChange_d (d : M →ₗ[R] R) (n : ℕ)
    (z : ExteriorAlgebra.exteriorPower S (n + 1) (S ⊗[R] M)) :
    exteriorDegreeToBaseChange n
        (exteriorDegreeDifferential (exteriorBaseChangeDifferential d) n z) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
        (exteriorDegreeDifferential d n) (exteriorDegreeToBaseChange (n + 1) z) := by
  apply exteriorBaseChangeDegreeInclusion_injective n
  rw [exteriorDegreeToBaseChange_inclusion, exteriorBaseChangeDegreeInclusion_d,
    exteriorDegreeToBaseChange_inclusion]
  exact (exteriorToBaseChange_contract d z.val).symm

end SerrePositivity.KST.DerivedBlowup
