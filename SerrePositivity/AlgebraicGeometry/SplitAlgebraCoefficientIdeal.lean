module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.CoefficientIdeal
public import Mathlib.Algebra.Algebra.Operations

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の自由な直和の直和因子となる代数の係数イデアル。
方針：代数の乗法を分裂写像によって直和の線形写像に延長する。
規約：分裂写像を明示的に入力し、その存在を公理や型クラスにしない。
使われ方：有限生成イデアルの係数から、基礎環上の有限生成 blowup 中心を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {ι : Type*}
  (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
  (hpe : p.comp e = LinearMap.id)

include p hpe

/--
概要：直和因子で表した代数の元の係数がイデアルに入れば、任意の代数元との積も同じ条件を満たす。
方針：乗法を e ∘ (b·) ∘ p として直和の線形自己写像に延長する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基礎環上の線形性だけを使う。
使われ方：代数イデアルの生成元の係数から全元の係数を生成する。
-/
theorem splitAlgebra_mul_coeff_mem (I : Ideal R) (b x : B)
    (hx : ∀ i, e x i ∈ I) (i : ι) : e (b * x) i ∈ I := by
  let T : (ι →₀ R) →ₗ[R] (ι →₀ R) := e.comp ((Algebra.lsmul R R B b).comp p)
  have hpx : p (e x) = x := LinearMap.congr_fun hpe x
  have h := finsupp_linearMap_coeff_mem T I (e x) hx i
  simpa only [T, LinearMap.comp_apply, hpx, Algebra.lsmul_apply, smul_eq_mul] using h

/--
概要：代数のイデアルを基礎環の直和に埋め込んで得る係数イデアル。
方針：イデアルの全元の全係数によるイデアルを取る。
規約：KST §5、Stacks 0810, Lemma 38.30.2、分裂の選択を定義には含めない。
使われ方：基底上の平坦化中心の候補。
-/
def splitAlgebraCoefficientIdeal (J : Ideal B) : Ideal R :=
  finsuppCoefficientIdeal (e '' (J : Set B))

/--
概要：係数イデアルは、代数イデアルの生成元の係数だけで生成できる。
方針：span の帰納法と乗法による係数の所属の保存を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、生成集合は有限とは限らない。
使われ方：有限生成中心を、元のイデアルの有限生成元から実際に選ぶ。
-/
theorem splitAlgebraCoefficientIdeal_span (s : Set B) :
    splitAlgebraCoefficientIdeal e (Ideal.span s) = finsuppCoefficientIdeal (e '' s) := by
  apply le_antisymm
  · apply (finsuppCoefficientIdeal_le_iff _ _).mpr
    rintro y ⟨x, hx, rfl⟩ i
    have hall : ∀ j, e x j ∈ finsuppCoefficientIdeal (e '' s) := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro j
        exact mem_finsuppCoefficientIdeal (s := e '' s) ⟨x, hx, rfl⟩ j
      | zero => simp
      | add x y _ _ hx hy =>
        intro j
        simpa only [map_add, Finsupp.add_apply] using Ideal.add_mem _ (hx j) (hy j)
      | smul b x _ hx => exact splitAlgebra_mul_coeff_mem e p hpe _ b x hx
    exact hall i
  · apply (finsuppCoefficientIdeal_le_iff _ _).mpr
    rintro y ⟨x, hx, rfl⟩ i
    exact mem_finsuppCoefficientIdeal (s := e '' (Ideal.span s : Set B))
      ⟨x, Ideal.subset_span hx, rfl⟩ i

/--
概要：有限生成の代数イデアルの係数イデアルは基礎環上有限生成。
方針：有限個の生成元の像に係数イデアルを還元し、それぞれの有限台を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基礎環の Noether 性は不要。
使われ方：平坦化の blowup に使う実際の有限生成中心。
-/
theorem splitAlgebraCoefficientIdeal_fg (J : Ideal B) (hJ : J.FG) :
    (splitAlgebraCoefficientIdeal e J).FG := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hJ
  rw [← hspan, splitAlgebraCoefficientIdeal_span e p hpe]
  exact finsuppCoefficientIdeal_fg (hs.image e)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
