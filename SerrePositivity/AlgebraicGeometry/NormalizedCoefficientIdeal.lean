module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientScalar
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientMembership
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Regular.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の係数の正則な共通因子を除いたイデアル。
方針：colon イデアルで共通因子を除き、係数イデアルのスカラー倍の公式で正則元を消去する。
規約：基礎環の正則性を使い、代数の整域性は仮定しない。
使われ方：基礎環の拡大素イデアルで元の代数イデアルを単項化する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]

/--
概要：明示的な直和への分裂を持つ代数では、基礎環の正則元の像も正則。
方針：積の等式を直和の各係数に移して基礎環で消去し、分裂の単射性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、平坦性の追加仮定は不要。
使われ方：係数中心の共通因子が代数側とその局所化でも正則であることを得る。
-/
theorem algebraMap_isRegular_of_split_coefficients
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (c : R) (hc : IsRegular c) :
    IsRegular (algebraMap R B c) := by
  have heinj : Function.Injective e :=
    Function.LeftInverse.injective (fun x => show p (e x) = x from LinearMap.congr_fun hpe x)
  have hleft : IsLeftRegular (algebraMap R B c) := by
    intro x y hxy
    apply heinj
    ext i
    apply hc.left
    have h := congrArg (fun z => e z i) hxy
    simpa only [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] using h
  exact ⟨hleft, hleft.right_of_commute (fun _ => mul_comm _ _)⟩

/--
概要：代数イデアルから基礎環の元の共通因子を除く colon イデアル。
方針：その元の代数への像との積が元のイデアルに入る元を取る。
規約：KST §5、Stacks 0810, Lemma 38.30.2、単元であるとは仮定しない。
使われ方：係数イデアルを単位イデアルへ正規化する。
-/
def normalizedCoefficientIdeal (c : R) (J : Ideal B) : Ideal B :=
  J.colon {algebraMap R B c}

/--
概要：代数イデアルの全元が共通因子で割り切れれば、colon イデアルとの積が元のイデアルに一致する。
方針：各元の可除表示と colon への所属を双方向に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、正則性はこの等式には不要。
使われ方：係数イデアルのスカラー倍の公式を適用する。
-/
theorem normalizedCoefficientIdeal_mul (c : R) (J : Ideal B)
    (hdiv : J ≤ Ideal.span {algebraMap R B c}) :
    Ideal.span {algebraMap R B c} * normalizedCoefficientIdeal c J = J := by
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    have h : d * algebraMap R B c ∈ J := Submodule.mem_colon_singleton.mp hd
    simpa only [mul_comm] using h
  · intro x hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hdiv hx)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨d, ?_, hd.symm⟩
    apply Submodule.mem_colon_singleton.mpr
    change d * algebraMap R B c ∈ J
    rw [mul_comm, ← hd]
    exact hx

/--
概要：係数イデアルが正則単項なら、共通因子を除いたイデアルの係数イデアルは単位イデアル。
方針：元のイデアルの積表示と係数イデアルのスカラー倍の公式から正則元を消去する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、係数表示の分裂を明示する。
使われ方：拡大された真のイデアルの外に正規化した元が存在することを得る。
-/
theorem normalizedCoefficientIdeal_coeff_eq_top
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (c : R) (J : Ideal B) (hc : IsRegular c)
    (hcoeff : splitAlgebraCoefficientIdeal e J = Ideal.span {c}) :
    splitAlgebraCoefficientIdeal e (normalizedCoefficientIdeal c J) = ⊤ := by
  have hdiv : J ≤ Ideal.span {algebraMap R B c} := by
    have h := (splitAlgebraCoefficientIdeal_le_iff e p hpe J (Ideal.span {c})).mp hcoeff.le
    simpa only [Ideal.map_span, Set.image_singleton] using h
  have hprod : Ideal.span {c} * splitAlgebraCoefficientIdeal e (normalizedCoefficientIdeal c J) =
      Ideal.span {c} := by
    rw [← splitAlgebraCoefficientIdeal_scalar, normalizedCoefficientIdeal_mul c J hdiv, hcoeff]
  have hmem : c ∈ Ideal.span {c} *
      splitAlgebraCoefficientIdeal e (normalizedCoefficientIdeal c J) :=
    hprod.symm ▸ Ideal.mem_span_singleton_self c
  obtain ⟨z, hz, hcz⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hz1 : z = 1 := hc.left (hcz.trans (mul_one c).symm)
  exact (Ideal.eq_top_iff_one _).mpr (hz1 ▸ hz)

/--
概要：正則な共通因子を除いたイデアルは、基礎環のいかなる真のイデアルの拡大にも含まれない。
方針：係数イデアルが単位であることと拡大イデアルへの包含の判定を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、素性はこの非包含には不要。
使われ方：拡大素イデアルでの局所化で正規化イデアルが単位になることを示す。
-/
theorem normalizedCoefficientIdeal_not_le_map
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (c : R) (J : Ideal B) (hc : IsRegular c)
    (hcoeff : splitAlgebraCoefficientIdeal e J = Ideal.span {c})
    (I : Ideal R) (hI : I ≠ ⊤) :
    ¬ normalizedCoefficientIdeal c J ≤ I.map (algebraMap R B) := by
  intro h
  have hle := (splitAlgebraCoefficientIdeal_le_iff e p hpe (normalizedCoefficientIdeal c J) I).mpr h
  rw [normalizedCoefficientIdeal_coeff_eq_top e p hpe c J hc hcoeff] at hle
  exact hI (top_unique hle)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
