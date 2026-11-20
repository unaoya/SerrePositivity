module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.MonomialOrderCoefficientMap
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
概要：KST §5、Stacks 051R の係数局所化後のイデアルの先頭次数被覆。
方針：局所化イデアルの元の分母を払い、単元スカラー倍と単射な係数変更の次数保存を使う。
規約：局所化写像の単射性を明示し、整域性は呼び出し側で用意する。
使われ方：局所化後の単元先頭係数の族から標準単項式基底を構成する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
attribute [local instance] MvPolynomial.algebraMvPolynomial

/--
概要：イデアルの先頭次数を覆う有限族は、単射な係数局所化後も拡大イデアルの先頭次数を覆う。
方針：分母を払ったイデアル元の先頭次数を、単元スカラー倍と係数写像の台保存で比較する。
規約：KST §5、Stacks 051R、次数比較は座標毎の順序。
使われ方：有限個の先頭係数を反転した多項式商の自由性。
-/
theorem leading_degree_cover_localization
    {σ R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [DecidableEq (MvPolynomial σ S)]
    (M : Submonoid R) [IsLocalization M S]
    (hι : Function.Injective (algebraMap R S))
    (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R)) (H : Ideal (MvPolynomial σ R))
    (hcover : ∀ h ∈ H, h ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree h) :
    ∀ h ∈ H.map (MvPolynomial.map (algebraMap R S)), h ≠ 0 →
      ∃ g ∈ G.image (MvPolynomial.map (algebraMap R S)), m.degree g ≤ m.degree h := by
  classical
  intro h hh hh0
  change h ∈ H.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) at hh
  obtain ⟨⟨g, s⟩, he⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M.map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ S)).mp hh
  obtain ⟨r, hr, hrs⟩ := s.property
  have hu : IsUnit (algebraMap R S r) := IsLocalization.map_units S (⟨r, hr⟩ : M)
  rw [← hrs, MvPolynomial.algebraMap_def, MvPolynomial.map_C] at he
  change h * MvPolynomial.C (algebraMap R S r) =
    MvPolynomial.map (algebraMap R S) g.val at he
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul] at he
  have hg0 : g.val ≠ 0 := by
    intro hg
    rw [hg, map_zero] at he
    exact hh0 (hu.smul_eq_zero.mp he)
  have hdeg : m.degree h = m.degree g.val := by
    have hd := congrArg m.degree he
    rwa [m.degree_smul_of_isRegular hu.isRegular,
      monomialOrder_degree_map_of_injective m (algebraMap R S) hι] at hd
  obtain ⟨g', hg', hgg⟩ := hcover g.val g.property hg0
  refine ⟨MvPolynomial.map (algebraMap R S) g', Finset.mem_image.mpr ⟨g', hg', rfl⟩, ?_⟩
  rw [monomialOrder_degree_map_of_injective m (algebraMap R S) hι, hdeg]
  exact hgg

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
