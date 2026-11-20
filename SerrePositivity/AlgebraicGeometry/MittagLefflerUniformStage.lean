module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.MittagLefflerCoevaluation
public import SerrePositivity.AlgebraicGeometry.LinearSequenceTensorZero

/-!
概要：KST §5、Stacks 05DP・059X の有限自由列の双対像に対する一様な後続段階。
方針：双対部分加群の商の積を試験し、Mittag–Leffler 性と有限段階でのテンソル零判定を使う。
規約：各段階の有限基底と実際の評価・遷移を明示する。
使われ方：有限自由列の双対像の安定化から射影性へ進むための一様化。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：各双対商で余評価の像が消えるなら、一つの後続段階の双対像が全ての商の核に含まれる。
方針：商写像の積の余評価を Mittag–Leffler 性で消し、有限段階判定と双対像の零判定を使う。
規約：KST §5、Stacks 05DP・059X、試験族の添字は任意、各基底は有限。
使われ方：双対遷移像の下降列を一つの段階で安定化する。
-/
theorem exists_stage_dual_range_le_iInf_of_mittagLeffler
    {R M J : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Type u) [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    {σ : ℕ → Type v} [∀ n, Fintype (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
    (a : ∀ n, F n →ₗ[R] F (n + 1)) (q : ∀ n, F n →ₗ[R] M)
    (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M)
    (n : ℕ) (L : J → Submodule R (Module.Dual R (F n)))
    (hL : ∀ j, (q n).rTensor (Module.Dual R (F n) ⧸ L j)
      (basisMappedCoevaluationTensor (b n) (L j).mkQ) = 0) :
    ∃ (k : ℕ) (h : n ≤ k),
      LinearMap.range (linearSequenceMap R F a n k h).dualMap ≤ ⨅ j, L j := by
  let P (j : J) := Module.Dual R (F n) ⧸ L j
  let ε (j : J) : Module.Dual R (F n) →ₗ[R] P j := (L j).mkQ
  have hz := mittagLeffler_basisMappedCoevaluationTensor_pi_eq_zero
    P (b n) (q n) ε hM hL
  obtain ⟨k, hk, hzero⟩ :=
    (linearSequence_rTensor_eq_zero_iff R F a q hq hker hcover (∀ j, P j) n
      (basisMappedCoevaluationTensor (b n) (LinearMap.pi ε))).mp hz
  have hinc := (basisMappedCoevaluationTensor_rTensor_eq_zero_iff
    (b n) (b k) (linearSequenceMap R F a n k hk) (LinearMap.pi ε)).mp hzero
  refine ⟨k, hk, le_iInf (fun j => ?_)⟩
  intro φ hφ
  have hε : (LinearMap.pi ε) φ = 0 := hinc hφ
  have hj := congrFun hε j
  have hmem : φ ∈ LinearMap.ker (L j).mkQ := hj
  simpa only [Submodule.ker_mkQ] using hmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
