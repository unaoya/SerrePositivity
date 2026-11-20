module

public import SerrePositivity.AlgebraicGeometry.LinearSequenceDirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
概要：KST §5、Stacks 05DP・059X の加群列のテンソル積における有限段階での零判定。
方針：二つの直極限実装の比較とテンソル積の可換同型から、有限段階の零判定へ戻す。
規約：試験加群の平坦性は不要、評価の核消去と像の被覆を明示する。
使われ方：Mittag–Leffler 性を有限自由列の双対像の安定化へ移す準備。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R : Type u) [CommRing R] (F : ℕ → Type u)
  [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
  (a : ∀ n, F n →ₗ[R] F (n + 1))
  {M : Type u} [AddCommGroup M] [Module R M]
  (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
  (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
  (hcover : (⨆ n, LinearMap.range (q n)) = ⊤)

/--
概要：直和の商による加群直極限も評価先の加群と実際に線形同型。
方針：二つの直極限の標準比較同型と構成済みの評価同型を合成する。
規約：KST §5、Stacks 05DP・059X、Mathlib のテンソル直極限 API の表示に合わせる。
使われ方：直極限とテンソル積の可換同型を評価写像に接続する。
-/
def linearSequenceModuleLimitEquiv :
    Module.DirectLimit F (linearSequenceMap R F a) ≃ₗ[R] M :=
  (Module.DirectLimit.linearEquiv F (linearSequenceMap R F a)).trans
    (linearSequenceDirectLimitEquiv R F a q hq hker hcover)

/--
概要：加群直極限の比較同型は各成分で元の評価写像を返す。
方針：標準直極限比較の成分公式と評価の定義を使う。
規約：KST §5、Stacks 05DP・059X、元の線形写像を保持する。
使われ方：各段階の右テンソル積と直極限評価の可換性。
-/
theorem linearSequenceModuleLimitEquiv_of (n : ℕ) (x : F n) :
    linearSequenceModuleLimitEquiv R F a q hq hker hcover
      (Module.DirectLimit.of R ℕ F (linearSequenceMap R F a) n x) = q n x := by
  simp only [linearSequenceModuleLimitEquiv, LinearEquiv.trans_apply,
    Module.DirectLimit.linearEquiv_of]
  rfl

include hq hker hcover in
/--
概要：各段階のテンソルの元の評価が零であることは、ある有限後続段階で零になることと同値。
方針：実際の評価同型を右テンソルし、直極限との可換同型と元の零判定を使う。
規約：KST §5、Stacks 05DP・059X、試験加群には平坦性・有限性を要求しない。
使われ方：積比較の単射性から有限自由列の一様な後続段階を取り出す。
-/
theorem linearSequence_rTensor_eq_zero_iff
    (P : Type u) [AddCommGroup P] [Module R P] (n : ℕ) (x : F n ⊗[R] P) :
    (q n).rTensor P x = 0 ↔
      ∃ (k : ℕ) (h : n ≤ k), (linearSequenceMap R F a n k h).rTensor P x = 0 := by
  let E := linearSequenceModuleLimitEquiv R F a q hq hker hcover
  have hcomp : E.toLinearMap.comp
      (Module.DirectLimit.of R ℕ F (linearSequenceMap R F a) n) = q n := by
    ext y
    exact linearSequenceModuleLimitEquiv_of R F a q hq hker hcover n y
  constructor
  · intro hx
    have hz : (Module.DirectLimit.of R ℕ F (linearSequenceMap R F a) n).rTensor P x = 0 := by
      apply (LinearEquiv.rTensor P E).injective
      rw [map_zero]
      change E.toLinearMap.rTensor P
        ((Module.DirectLimit.of R ℕ F (linearSequenceMap R F a) n).rTensor P x) = 0
      rw [← LinearMap.rTensor_comp_apply, hcomp]
      exact hx
    have hzero : Module.DirectLimit.of R ℕ (fun i => F i ⊗[R] P)
        (fun i j h => (linearSequenceMap R F a i j h).rTensor P) n x = 0 := by
      have h := congrArg (TensorProduct.directLimitLeft (linearSequenceMap R F a) P) hz
      simpa only [TensorProduct.directLimitLeft_rTensor_of, map_zero] using h
    exact Module.DirectLimit.of.zero_exact hzero
  · rintro ⟨k, hk, hx⟩
    have heval : (q k).comp (linearSequenceMap R F a n k hk) = q n := by
      ext y
      exact linearSequenceMap_eval R F a q hq n k hk y
    rw [← heval, LinearMap.rTensor_comp_apply, hx, map_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
