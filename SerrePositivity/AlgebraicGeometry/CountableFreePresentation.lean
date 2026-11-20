module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.NoetherianCountableGeneration

/-!
概要：KST §5、Stacks 05DP・059X の Noether 基底上の可算自由表示。
方針：可算生成集合から自由全射を作り、その核の可算生成集合から関係式の写像を作る。
規約：自由加群は実際の有限台関数加群、完全性は像と核の等式で述べる。
使われ方：可算生成平坦 Mittag–Leffler 加群の射影性判定の表示側の準備。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：可算生成加群は可算基底を持つ自由加群の実際の全射像。
方針：可算生成集合を添字とする有限線形結合写像を使う。
規約：KST §5、Stacks 05DP・059X、Noether 性はこの全射の構成には不要。
使われ方：可算生成加群の自由表示の生成元側。
-/
theorem exists_countable_free_surjection
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : HasCountableGeneratingSet R M) :
    ∃ (κ : Type u) (_ : Countable κ) (q : (κ →₀ R) →ₗ[R] M), Function.Surjective q := by
  obtain ⟨S, hSc, hS⟩ := hM
  refine ⟨S, hSc.to_subtype, Finsupp.linearCombination R (Subtype.val : S → M), ?_⟩
  apply LinearMap.range_eq_top.mp
  rw [← Finsupp.span_eq_range_linearCombination]
  exact hS

/--
概要：Noether 基底上の可算生成加群には可算個の生成元と関係式による実際の自由表示がある。
方針：自由全射の核へ可算生成部分加群の補題を適用し、その自由全射を包含と合成する。
規約：KST §5、Stacks 05DP・059X、第二写像の像が第一写像の核に一致する。
使われ方：有限自由段階による射影性判定へ進むための具体的な可算表示。
-/
theorem exists_countable_free_presentation
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    (hM : HasCountableGeneratingSet R M) :
    ∃ (κ ν : Type u) (_ : Countable κ) (_ : Countable ν)
      (q : (κ →₀ R) →ₗ[R] M) (h : (ν →₀ R) →ₗ[R] (κ →₀ R)),
      Function.Surjective q ∧ LinearMap.range h = LinearMap.ker q := by
  classical
  obtain ⟨κ, hκ, q, hq⟩ := exists_countable_free_surjection hM
  let : Countable κ := hκ
  have hfree : HasCountableGeneratingSet R (κ →₀ R) :=
    hasCountableGeneratingSet_of_basis (Finsupp.basisSingleOne : Module.Basis κ R (κ →₀ R))
  obtain ⟨ν, hν, k, hk⟩ := exists_countable_free_surjection (hfree.submodule (LinearMap.ker q))
  refine ⟨κ, ν, hκ, hν, q, (LinearMap.ker q).subtype.comp k, hq, ?_⟩
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hk, Submodule.map_top,
    Submodule.range_subtype]

/--
概要：Noether 基礎環の有限型代数上有限な加群には、基礎環上可算個の生成元・関係式の自由表示がある。
方針：単項式と有限生成元による可算生成性を、可算自由表示の存在へ渡す。
規約：KST §5、Stacks 05DP・059X、基礎環の集合としての可算性は不要。
使われ方：幾何学的整な有限型代数の射影性の原典経路への入力。
-/
theorem exists_countable_free_presentation_of_finiteType_finite
    (R B M : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M] :
    ∃ (κ ν : Type u) (_ : Countable κ) (_ : Countable ν)
      (q : (κ →₀ R) →ₗ[R] M) (h : (ν →₀ R) →ₗ[R] (κ →₀ R)),
      Function.Surjective q ∧ LinearMap.range h = LinearMap.ker q :=
  exists_countable_free_presentation (hasCountableGeneratingSet_of_finiteType_finite R B M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
