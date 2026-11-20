module

public import SerrePositivity.AlgebraicGeometry.MittagLefflerDualStabilization
public import SerrePositivity.AlgebraicGeometry.FiniteDualFactorization

/-!
概要：KST §5、Stacks 05DP・059X の有限自由列の任意の加群値の Hom 逆系の像の安定化。
方針：係数環値の双対像の安定化を、有限双対による任意の値域への因子化へ移す。
規約：安定化段階は値域加群に依存せず、値域の宇宙も任意。
使われ方：全射への整合的な持ち上げを可算逆系から構成する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry

/--
概要：Mittag–Leffler 加群を表す有限自由列の前合成像は、任意の値域で同じ有限後続段階から安定する。
方針：双対遷移像の安定化を取り、その等号から各値域への因子化の同値を得る。
規約：KST §5、Stacks 05DP・059X、値域の有限性・平坦性と宇宙の制限は不要。
使われ方：Hom 逆系を全射の核にも適用し、整合的な持ち上げを構成する。
-/
theorem exists_stable_hom_factorizations_of_mittagLeffler
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Type u) [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    {σ : ℕ → Type v} [∀ n, Finite (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
    (a : ∀ n, F n →ₗ[R] F (n + 1)) (q : ∀ n, F n →ₗ[R] M)
    (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M)
    (n : ℕ) :
    ∃ (k : ℕ) (hk : n ≤ k), ∀ (ℓ : ℕ) (hkℓ : k ≤ ℓ)
      (N : Type w) [AddCommGroup N] [Module R N] (h : F n →ₗ[R] N),
      (∃ φ : F ℓ →ₗ[R] N, φ.comp (linearSequenceMap R F a n ℓ (hk.trans hkℓ)) = h) ↔
        ∃ ψ : F k →ₗ[R] N, ψ.comp (linearSequenceMap R F a n k hk) = h := by
  obtain ⟨k, hk, hstable⟩ := exists_stable_dual_ranges_of_mittagLeffler
    F b a q hq hker hcover hM n
  refine ⟨k, hk, ?_⟩
  intro ℓ hkℓ N hN hRN h
  exact linearMap_factorization_iff_of_dual_ranges_eq (b ℓ) (b k)
    (linearSequenceMap R F a n ℓ (hk.trans hkℓ)) (linearSequenceMap R F a n k hk)
    (hstable ℓ hkℓ) h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
