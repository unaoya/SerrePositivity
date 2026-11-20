module

public import SerrePositivity.AlgebraicGeometry.NormalizedCoefficientIdeal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の拡大素イデアルでの係数イデアルの正則単項化。
方針：正規化した colon イデアルの非包含から局所化での単位性を導く。
規約：拡大イデアルが素であることを明示し、幾何学的整ファイバーからの素性は別に扱う。
使われ方：係数 blowup 後の代数の特別な局所環で小行列式を正則単項にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：係数イデアルが正則単項なら、基礎環の真のイデアルの拡大が素となる各局所環で元のイデアルも正則単項。
方針：colon イデアルの像が単位となる元を選び、元のイデアルの積表示を局所化する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、分裂と拡大イデアルの素性を明示する。
使われ方：有限型加群の平坦化で特別な局所環に生成元除去の補題を適用する。
-/
theorem coefficientIdeal_regular_principal_at_extended_prime
    {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (c : R) (J : Ideal B) (hc : IsRegular c)
    (hcoeff : splitAlgebraCoefficientIdeal e J = Ideal.span {c})
    (I : Ideal R) (hI : I ≠ ⊤) [(I.map (algebraMap R B)).IsPrime] :
    let L := Localization.AtPrime (I.map (algebraMap R B))
    algebraMap B L (algebraMap R B c) ∈ nonZeroDivisors L ∧
      J.map (algebraMap B L) = Ideal.span {algebraMap B L (algebraMap R B c)} := by
  classical
  let L := Localization.AtPrime (I.map (algebraMap R B))
  let K := normalizedCoefficientIdeal c J
  have hnot : ¬ K ≤ I.map (algebraMap R B) :=
    normalizedCoefficientIdeal_not_le_map e p hpe c J hc hcoeff I hI
  have hex : ∃ g : B, g ∈ K ∧ g ∉ I.map (algebraMap R B) := by
    by_contra h
    apply hnot
    intro x hx
    by_contra hxI
    exact h ⟨x, hx, hxI⟩
  obtain ⟨g, hg, hgI⟩ := hex
  have hK : K.map (algebraMap B L) = ⊤ :=
    (K.map (algebraMap B L)).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units (M := (I.map (algebraMap R B)).primeCompl) L ⟨g, hgI⟩)
  have hdiv : J ≤ Ideal.span {algebraMap R B c} := by
    have h := (splitAlgebraCoefficientIdeal_le_iff e p hpe J (Ideal.span {c})).mp hcoeff.le
    simpa only [Ideal.map_span, Set.image_singleton] using h
  constructor
  · exact IsLocalization.nonZeroDivisors_le_comap (S := L)
      (I.map (algebraMap R B)).primeCompl
      (isRegular_iff_mem_nonZeroDivisors.mp
        (algebraMap_isRegular_of_split_coefficients e p hpe c hc))
  · rw [← normalizedCoefficientIdeal_mul c J hdiv, Ideal.map_mul]
    change (Ideal.span {algebraMap R B c}).map (algebraMap B L) * K.map (algebraMap B L) = _
    rw [hK, Ideal.mul_top, Ideal.map_span, Set.image_singleton]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
