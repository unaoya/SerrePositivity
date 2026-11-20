module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の共通因子と純変換の境界元の比較。
方針：一方の元が他方の冪を割るとき、冪ねじれの包含から実際の商の全射を作る。
規約：二つの境界元は区別し、純変換の同型は主張しない。
使われ方：小行列式の共通因子で消える擬関係式を元の境界に沿う純変換でも除く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (c f : R) (M : Type*) [AddCommGroup M] [Module R M]
  (N : ℕ) (hcf : c ∣ f ^ N)

include N hcf

/--
概要：一方の境界元が他方の冪を割れば、前者の冪ねじれは後者の冪ねじれに含まれる。
方針：可除表示を冪にし、元を消す冪の等式と組み合わせる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、指数は積を取る。
使われ方：異なる元に沿う二つの純変換の商写像を構成する。
-/
theorem boundaryTorsion_le_of_dvd_pow : boundaryTorsion c M ≤ boundaryTorsion f M := by
  intro m hm
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff c M m).mp hm
  obtain ⟨r, hr⟩ := hcf
  apply (mem_boundaryTorsion_iff f M m).mpr
  refine ⟨N * n, ?_⟩
  rw [pow_mul, hr, mul_pow, mul_comm (c ^ n) (r ^ n), mul_smul, hn, smul_zero]

/--
概要：一方の境界元が他方の冪を割る場合の純変換の実際の比較写像。
方針：冪ねじれの包含で商写像を降ろす。
規約：KST §5、Stacks 0810, Lemma 38.30.2、共通因子側から元の境界側への向き。
使われ方：共通因子による生成元削減を元の純変換に移す。
-/
def modulePureTransformBoundaryMap : modulePureTransform c M →ₗ[R] modulePureTransform f M :=
  (boundaryTorsion c M).liftQ (boundaryTorsion f M).mkQ (by
    rw [Submodule.ker_mkQ]
    exact boundaryTorsion_le_of_dvd_pow c f M N hcf)

/--
概要：異なる境界元の純変換の比較写像は元の加群からの商写像と両立。
方針：商からの写像の定義を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：比較写像を通した生成全射の照合。
-/
theorem modulePureTransformBoundaryMap_mk (m : M) :
    modulePureTransformBoundaryMap c f M N hcf ((boundaryTorsion c M).mkQ m) =
      (boundaryTorsion f M).mkQ m := rfl

/--
概要：異なる境界元に沿う純変換の比較写像は全射。
方針：任意の商の元を元の加群の元で代表する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、同型性は主張しない。
使われ方：共通因子による生成元の上界を元の境界の純変換へ移す。
-/
theorem modulePureTransformBoundaryMap_surjective :
    Function.Surjective (modulePureTransformBoundaryMap c f M N hcf) := by
  intro y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) y
  exact ⟨(boundaryTorsion c M).mkQ m, rfl⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
