module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteLeadingDegreeCover
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
概要：KST §5、Stacks 051R の有限個の先頭係数を同時に単元にする局所化。
方針：先頭係数の積を反転し、各先頭係数がその積を割ることを使う。
規約：整域上では非零多項式の族から非零な反転元を選ぶ。
使われ方：一般自由性の標準単項式基底に必要な単元係数。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：有限個の非零多項式の先頭係数の積は、整域上で非零。
方針：各先頭係数の非零性と有限積の非零性を使う。
規約：KST §5、Stacks 051R、空積は一として扱う。
使われ方：一般自由性で反転する元の非零性。
-/
theorem prod_leadingCoeff_ne_zero
    {σ R : Type u} [CommRing R] [IsDomain R] (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ R)) (hG : ∀ g ∈ G, g ≠ 0) :
    (∏ g ∈ G, m.leadingCoeff g) ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun g hg => m.leadingCoeff_ne_zero_iff.mpr (hG g hg))

/--
概要：先頭係数の有限積を反転すると、各先頭係数の像は単元。
方針：各係数が積を割ることと、局所化した積の単元性を使う。
規約：KST §5、Stacks 051R、この単元性自体には整域性は不要。
使われ方：係数変更した多項式の先頭係数を除法アルゴリズムへ渡す。
-/
theorem isUnit_leadingCoeff_in_prod_localization
    {σ R : Type u} [CommRing R] (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ R)) (g : MvPolynomial σ R) (hg : g ∈ G) :
    IsUnit (algebraMap R (Localization.Away (∏ h ∈ G, m.leadingCoeff h)) (m.leadingCoeff g)) := by
  classical
  exact isUnit_of_dvd_unit
    (map_dvd (algebraMap R (Localization.Away (∏ h ∈ G, m.leadingCoeff h)))
      (Finset.dvd_prod_of_mem (fun h => m.leadingCoeff h) hg))
    (IsLocalization.Away.algebraMap_isUnit (∏ h ∈ G, m.leadingCoeff h))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
