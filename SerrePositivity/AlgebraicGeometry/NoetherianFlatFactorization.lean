module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：KST §5、Stacks 05DP・059X・058E の Noether 基底上の有限自由近似。
方針：有限生成な像の有限表示性から平坦加群への因子化を選び、包含の単射性で核を照合する。
規約：標的の平坦加群自体の有限性・射影性は仮定しない。
使われ方：可算自由表示から有限自由加群の列を構成する準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：平坦加群の有限生成部分加群の包含は、有限自由加群への単射を通じて因子化する。
方針：Noether 基底上の有限表示性と Mathlib の平坦加群への有限自由因子化を使う。
規約：KST §5、Stacks 05DP・059X・058E、実際の因子化写像と可換式を返す。
使われ方：可算生成平坦加群の有限自由段階を取る。
-/
theorem exists_finiteFree_factorization_of_fg_submodule
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (N : Submodule R M) (hN : N.FG) :
    ∃ (k : ℕ) (a : N →ₗ[R] (Fin k →₀ R)) (b : (Fin k →₀ R) →ₗ[R] M),
      b.comp a = N.subtype ∧ Function.Injective a := by
  let : Module.Finite R N := Module.Finite.of_fg hN
  let : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  obtain ⟨k, a, b, hfac⟩ := Module.Flat.exists_factorization_of_finitePresentation N.subtype
  refine ⟨k, a, b, hfac.symm, ?_⟩
  intro x y hxy
  apply Subtype.ext
  change N.subtype x = N.subtype y
  rw [hfac]
  exact congrArg b hxy

/--
概要：有限加群から平坦加群への写像は、元の核を正確に保つ有限自由因子化を持つ。
方針：有限生成な像の包含を有限自由加群へ因子化し、像への制限と単射を合成する。
規約：KST §5、Stacks 05DP・059X・058E、基礎環は Noether、標的は有限とは限らない。
使われ方：有限自由近似で元の関係式を一つの段階で全て消す。
-/
theorem exists_finiteFree_factorization_same_kernel
    {R P M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (f : P →ₗ[R] M) :
    ∃ (k : ℕ) (a : P →ₗ[R] (Fin k →₀ R)) (b : (Fin k →₀ R) →ₗ[R] M),
      b.comp a = f ∧ LinearMap.ker a = LinearMap.ker f := by
  have hf : (LinearMap.range f).FG := by
    simpa only [Submodule.map_top] using
      (Module.Finite.fg_top (R := R) (M := P)).map f
  obtain ⟨k, a, b, hba, ha⟩ :=
    exists_finiteFree_factorization_of_fg_submodule (LinearMap.range f) hf
  refine ⟨k, a.comp f.rangeRestrict, b, ?_, ?_⟩
  · ext x
    change (b.comp a) (f.rangeRestrict x) = f x
    rw [hba]
    rfl
  · ext x
    change a (f.rangeRestrict x) = 0 ↔ f x = 0
    constructor
    · intro hx
      have h0 : f.rangeRestrict x = 0 := ha (by simpa using hx)
      exact congrArg Subtype.val h0
    · intro hx
      have h0 : f.rangeRestrict x = 0 := Subtype.ext hx
      simp only [h0, map_zero]

/--
概要：有限加群から平坦加群への核を保つ有限自由因子化を取り、さらに指定した一元を評価像に含められる。
方針：元の有限加群へ係数環を一つ直積し、新しい元を送る写像の核を保つ因子化を使う。
規約：KST §5、Stacks 05DP・059X・058E、Noether 基底、平坦な標的は有限とは限らない。
使われ方：可算個の生成元を一つずつ含める有限自由近似の逐次構成。
-/
theorem exists_finiteFree_factorization_same_kernel_and_element
    {R P M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (f : P →ₗ[R] M) (m : M) :
    ∃ (k : ℕ) (a : P →ₗ[R] (Fin k →₀ R)) (b : (Fin k →₀ R) →ₗ[R] M)
      (v : Fin k →₀ R), b.comp a = f ∧ LinearMap.ker a = LinearMap.ker f ∧ b v = m := by
  let f' : (P × R) →ₗ[R] M := f.coprod (LinearMap.toSpanSingleton R M m)
  obtain ⟨k, a', b, hba, hker⟩ := exists_finiteFree_factorization_same_kernel f'
  let a := a'.comp (LinearMap.inl R P R)
  refine ⟨k, a, b, a' (0, 1), ?_, ?_, ?_⟩
  · ext x
    have h := congrArg (fun g : (P × R) →ₗ[R] M => g (x, 0)) hba
    simpa [a, f', LinearMap.comp_apply] using h
  · ext x
    have h := congrArg (fun L : Submodule R (P × R) => (x, 0) ∈ L) hker
    simpa [a, f', LinearMap.mem_ker, LinearMap.comp_apply] using Iff.of_eq h
  · have h := congrArg (fun g : (P × R) →ₗ[R] M => g (0, 1)) hba
    simpa [f', LinearMap.comp_apply] using h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
