module

public import SerrePositivity.KST.DerivedBlowup.ExteriorTensorDegree

/-!
概要：KST Def3.1 の外積代数の基底変更同型を同次外積へ制限する。
方針：逆写像の同次性と tensor 包含の分裂単射性で両側の逆元律を示す。
規約：係数環の平坦性と2の可逆性は仮定しない。
使われ方：Koszul 複体の項ごとのスカラー拡大同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：逆基底変更の純粋 tensor 上の一般公式。
方針：代数 tensor の lift を評価する。
規約：KST Def3.1。使われ方：逆基底変更の同次性。 -/
theorem exteriorOfBaseChange_tmul (s : S) (z : ExteriorAlgebra R M) :
    exteriorOfBaseChange (s ⊗ₜ[R] z) = s • exteriorOfBaseChangeAux z := by
  change algebraMap S (ExteriorAlgebra S (S ⊗[R] M)) s *
    exteriorOfBaseChangeAux (R := R) (S := S) z = _
  exact (Algebra.smul_def _ _).symm

/-- 概要：元の外積から変更後の外積への写像は同次次数を保つ。
方針：同次外積の係数・和・生成元積による帰納法。
規約：KST Def3.1。使われ方：逆基底変更の同次性の生成元部分。 -/
theorem exteriorOfBaseChangeAux_mem_degree (n : ℕ) (z : ExteriorAlgebra R M)
    (hz : z ∈ ExteriorAlgebra.exteriorPower R n M) :
    exteriorOfBaseChangeAux (R := R) (S := S) z ∈
      ExteriorAlgebra.exteriorPower S n (S ⊗[R] M) := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S _ r]
    exact Submodule.algebraMap_mem _
  | add _ _ _ _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | mem_mul _ hx _ _ _ hy =>
    obtain ⟨x, rfl⟩ := hx
    rw [map_mul, exteriorOfBaseChangeAux_ι]
    have hg : ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] x) ∈
        ExteriorAlgebra.exteriorPower S 1 (S ⊗[R] M) := by
      simp only [ExteriorAlgebra.exteriorPower, pow_one]
      exact LinearMap.mem_range_self _ _
    simpa only [Nat.one_add] using SetLike.mul_mem_graded hg hy

/-- 概要：逆基底変更写像は tensor の同次部分を同次外積へ送る。
方針：同次包含の像の tensor を取り、純粋 tensor と和で帰納する。
規約：KST Def3.1。使われ方：逆基底変更写像の次数別制限。 -/
theorem exteriorOfBaseChange_mem_degree (n : ℕ)
    (z : S ⊗[R] ExteriorAlgebra R M) (hz : z ∈ exteriorTensorDegree n) :
    exteriorOfBaseChange z ∈ ExteriorAlgebra.exteriorPower S n (S ⊗[R] M) := by
  obtain ⟨z, rfl⟩ := hz
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    change exteriorOfBaseChange (s ⊗ₜ[R] z.val) ∈ _
    rw [exteriorOfBaseChange_tmul]
    exact Submodule.smul_mem _ s (exteriorOfBaseChangeAux_mem_degree n z.val z.property)
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

/-- 概要：tensor の同次部分では包含と射影の逆順の合成も恒等。
方針：像の元を取り、射影と包含の左逆を使う。
規約：KST Def3.1。使われ方：次数別基底変更同型の逆元律。 -/
theorem exteriorBaseChangeDegreeInclusion_projection (n : ℕ)
    (z : S ⊗[R] ExteriorAlgebra R M) (hz : z ∈ exteriorTensorDegree n) :
    exteriorBaseChangeDegreeInclusion n (exteriorBaseChangeDegreeProjection n z) = z := by
  obtain ⟨z, rfl⟩ := hz
  rw [exteriorBaseChangeDegreeProjection_inclusion]

/-- 概要：基底変更後の第n外積から元の第n外積の tensor への写像。
方針：総外積の基底変更の後に次数射影を合成する。
規約：KST Def3.1。使われ方：次数別基底変更同型の順写像。 -/
def exteriorDegreeToBaseChange (n : ℕ) :
    ExteriorAlgebra.exteriorPower S n (S ⊗[R] M) →ₗ[S]
      S ⊗[R] ExteriorAlgebra.exteriorPower R n M :=
  (exteriorBaseChangeDegreeProjection n).comp
    (exteriorToBaseChange.toLinearMap.comp (ExteriorAlgebra.exteriorPower S n (S ⊗[R] M)).subtype)

/-- 概要：元の第n外積の tensor から変更後の第n外積への写像。
方針：総外積の逆基底変更を同次部分へ制限する。
規約：KST Def3.1。使われ方：次数別基底変更同型の逆写像。 -/
def exteriorDegreeOfBaseChange (n : ℕ) :
    S ⊗[R] ExteriorAlgebra.exteriorPower R n M →ₗ[S]
      ExteriorAlgebra.exteriorPower S n (S ⊗[R] M) :=
  (exteriorOfBaseChange.toLinearMap.comp (exteriorBaseChangeDegreeInclusion n)).codRestrict _
    (fun z => exteriorOfBaseChange_mem_degree n _ ⟨z, rfl⟩)

/-- 概要：任意可換環へのスカラー拡大は各同次外積と可換。
方針：総外積の同型と分裂同次包含から両側逆を示す。
規約：KST Def3.1、平坦性不要。使われ方：Koszul 複体の各項の基底変更同型。 -/
def exteriorDegreeBaseChangeEquiv (n : ℕ) :
    ExteriorAlgebra.exteriorPower S n (S ⊗[R] M) ≃ₗ[S]
      S ⊗[R] ExteriorAlgebra.exteriorPower R n M :=
  LinearEquiv.ofLinearMap (exteriorDegreeToBaseChange n) (exteriorDegreeOfBaseChange n) (by
    apply LinearMap.ext
    intro z
    change exteriorBaseChangeDegreeProjection n
      (exteriorToBaseChange (exteriorOfBaseChange (exteriorBaseChangeDegreeInclusion n z))) = z
    have h := AlgHom.congr_fun (exteriorToBaseChange_comp_of (R := R) (S := S) (M := M))
      (exteriorBaseChangeDegreeInclusion n z)
    rw [show exteriorToBaseChange (exteriorOfBaseChange (exteriorBaseChangeDegreeInclusion n z)) =
      exteriorBaseChangeDegreeInclusion n z from h]
    exact exteriorBaseChangeDegreeProjection_inclusion n z) (by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change exteriorOfBaseChange (exteriorBaseChangeDegreeInclusion n
      (exteriorBaseChangeDegreeProjection n (exteriorToBaseChange z.val))) = z.val
    rw [exteriorBaseChangeDegreeInclusion_projection n _
      (exteriorToBaseChange_mem_degree n z.val z.property)]
    exact AlgHom.congr_fun exteriorOfBaseChange_comp_to z.val)

end SerrePositivity.KST.DerivedBlowup
