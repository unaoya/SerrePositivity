module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
概要：KST §5、Stacks 051R の単射な係数変更による先頭次数と先頭係数の保存。
方針：係数変更が台を正確に保つことを単項式順序の次数の定義に使う。
規約：零多項式も含め、係数環の整域性は要求しない。
使われ方：非零元での局所化後の先頭単項式の被覆。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：単射な係数変更は単項式順序による先頭次数を保つ。
方針：台の一致を先頭次数の有限上限の定義へ代入する。
規約：KST §5、Stacks 051R、零多項式も含む。
使われ方：局所化イデアルの分母を払った元との先頭次数の比較。
-/
theorem monomialOrder_degree_map_of_injective
    {σ R S : Type u} [CommRing R] [CommRing S] (m : MonomialOrder σ)
    (φ : R →+* S) (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (MvPolynomial.map φ f) = m.degree f := by
  simp only [MonomialOrder.degree, MvPolynomial.support_map_of_injective f hφ]

/--
概要：単射な係数変更の先頭係数は、元の先頭係数の像。
方針：保存された先頭次数で係数変更の係数公式を使う。
規約：KST §5、Stacks 051R、係数写像を明示する。
使われ方：局所化した先頭係数の単元性。
-/
theorem monomialOrder_leadingCoeff_map_of_injective
    {σ R S : Type u} [CommRing R] [CommRing S] (m : MonomialOrder σ)
    (φ : R →+* S) (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (MvPolynomial.map φ f) = φ (m.leadingCoeff f) := by
  simp only [MonomialOrder.leadingCoeff, monomialOrder_degree_map_of_injective m φ hφ,
    MvPolynomial.coeff_map]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
