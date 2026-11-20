module

public import SerrePositivity.AlgebraicGeometry.LeadingCoefficientLocalization
public import SerrePositivity.AlgebraicGeometry.LocalizedLeadingDegreeCover
public import SerrePositivity.AlgebraicGeometry.StandardMonomialQuotient

/-!
概要：KST §5、Stacks 051R の有限変数多項式商の一般自由性。
方針：有限個の先頭次数を選び、その先頭係数の積を反転して標準単項式基底を構成する。
規約：係数環は整域。イデアルの有限生成性を別の仮定として要求しない。
使われ方：有限型代数の多項式表示に対する一般自由性。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：整域の有限変数多項式商は、一つの非零係数を反転すると反転した係数環上自由。
方針：先頭次数の有限被覆と先頭係数の単元化を、標準単項式商の実際の基底へ渡す。
規約：KST §5、Stacks 051R、商は係数変更後のイデアルで定める。
使われ方：有限型代数の一般自由性と 05FS の射影性の存在。
-/
theorem exists_nonzero_free_polynomial_quotient_localization
    {σ R : Type u} [Finite σ] [CommRing R] [IsDomain R]
    (m : MonomialOrder σ) (H : Ideal (MvPolynomial σ R)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (MvPolynomial σ (Localization.Away f) ⧸
          H.map (MvPolynomial.map (algebraMap R (Localization.Away f)))) := by
  classical
  obtain ⟨G, hG, hcover⟩ := exists_finite_leading_degree_cover m H
  let f := ∏ g ∈ G, m.leadingCoeff g
  have hf : f ≠ 0 := prod_leadingCoeff_ne_zero m G (fun g hg => (hG g hg).2)
  let S := Localization.Away f
  have hι : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  let φ := MvPolynomial.map (σ := σ) (algebraMap R S)
  let G' := G.image φ
  let H' := H.map φ
  have hG' : ∀ g ∈ G', g ∈ H' := by
    intro g hg
    obtain ⟨g₀, hg₀, heq⟩ := Finset.mem_image.mp (show g ∈ G.image φ from hg)
    subst g
    exact Ideal.mem_map_of_mem φ (hG g₀ hg₀).1
  have hu : ∀ g ∈ G', IsUnit (m.leadingCoeff g) := by
    intro g hg
    obtain ⟨g₀, hg₀, heq⟩ := Finset.mem_image.mp (show g ∈ G.image φ from hg)
    subst g
    rw [monomialOrder_leadingCoeff_map_of_injective m (algebraMap R S) hι]
    exact isUnit_leadingCoeff_in_prod_localization m G g₀ hg₀
  have hcover' : ∀ h ∈ H', h ≠ 0 → ∃ g ∈ G', m.degree g ≤ m.degree h :=
    leading_degree_cover_localization (Submonoid.powers f) hι m G H hcover
  refine ⟨f, hf, ?_⟩
  exact Module.Free.of_basis (standardMonomialQuotientBasis m G' H' hG' hu hcover')

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
