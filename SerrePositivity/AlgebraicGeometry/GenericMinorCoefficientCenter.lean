module

public import SerrePositivity.AlgebraicGeometry.CoefficientBlowupCenter
public import SerrePositivity.AlgebraicGeometry.BaseChangedMinorFreeCriterion
public import Mathlib.RingTheory.Localization.Ideal

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の境界外の局所階数から選ぶ実際の係数中心。
方針：局所化された小行列式の単位性から拡大素イデアルへの非包含を得る。
規約：分裂表示と特別な局所環での射影性・階数を明示し、一般形の平坦化は別に残す。
使われ方：有限型加群の表示行列から具体的な admissible 中心を選ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：素点で局所化したイデアルが単位なら、そのイデアルは元の素イデアルに含まれない。
方針：包含を仮定すると素補集合と交わらず、局所化像が真のイデアルになることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：境界外の局所自由性から係数中心の admissible 性へ進む。
-/
theorem not_le_prime_of_atPrime_map_eq_top {B : Type*} [CommRing B]
    (P J : Ideal B) [P.IsPrime]
    (hJ : J.map (algebraMap B (Localization.AtPrime P)) = ⊤) : ¬ J ≤ P := by
  intro hle
  have hdis : Disjoint (P.primeCompl : Set B) (J : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxJ
    exact hx (hle hxJ)
  exact ((IsLocalization.map_algebraMap_ne_top_iff_disjoint
    (M := P.primeCompl) (S := Localization.AtPrime P) J).mpr hdis) hJ

/--
概要：境界外の拡大素点で所定階数を持つ表示から、小行列式の係数による有限生成 admissible 中心を構成する。
方針：基底変更した対象の階数で小行列式の像を単位とし、非包含から係数中心の境界冪を得る。
規約：KST §5、Stacks 0810, Lemma 38.30.2、拡大素性と射影性は幾何学的入力として明示する。
使われ方：Noether 有限型特殊形の実際の平坦化中心の構成の一段階。
-/
theorem generic_minor_coefficient_center_fg_complement
    {R B M ι m n : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Fintype m] [Finite n]
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B) (hpe : p.comp e = LinearMap.id)
    (H : Matrix m n B) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q) (f : R) (r : ℕ)
    (hprime : ∀ P : Ideal R, P.IsPrime → (P.map (algebraMap R B)).IsPrime)
    (hgeneric : ∀ (P : Ideal R) (hP : P.IsPrime), f ∉ P →
      letI : (P.map (algebraMap R B)).IsPrime := hprime P hP
      let L := Localization.AtPrime (P.map (algebraMap R B))
      Module.Projective L (L ⊗[B] M) ∧ Module.finrank L (L ⊗[B] M) = r) :
    (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e
      (matrixMinorIdeal H (Fintype.card m - r)))).FG ∧
      affineCenterComplement (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e
        (matrixMinorIdeal H (Fintype.card m - r)))) = PrimeSpectrum.basicOpen f := by
  classical
  apply coefficientBlowupCenter_fg_complement e p hpe f _ (matrixMinorIdeal_fg H _)
  intro P hP hfP
  let : (P.map (algebraMap R B)).IsPrime := hprime P hP
  let L := Localization.AtPrime (P.map (algebraMap R B))
  have hg := hgeneric P hP hfP
  have : Module.Projective L (L ⊗[B] M) := hg.1
  have hrank : Module.finrank L (L ⊗[B] M) = r := hg.2
  have hpat := minorIdeal_images_at_tensor_finrank (C := L) H q hq hH
  have hunit : (matrixMinorIdeal H (Fintype.card m - r)).map (algebraMap B L) = ⊤ := by
    simpa only [hrank] using hpat.1
  apply not_le_prime_of_atPrime_map_eq_top (P.map (algebraMap R B))
  exact hunit

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
