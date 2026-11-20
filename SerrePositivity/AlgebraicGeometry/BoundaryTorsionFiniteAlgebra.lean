module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryTorsionLocalization
public import Mathlib.RingTheory.FiniteType

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の Noether 代数上有限な加群の一様な境界ねじれ。
方針：拡大環上の境界ねじれの冪消滅を基礎環のスカラー作用へ戻す。
規約：加群の基礎環上の有限性を要求しない。
使われ方：有限型代数上の有限加群の純変換の追加基底変更。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
  [Module.Finite B M]

/--
概要：Noether 代数上有限な加群の基礎環に関する境界ねじれは一様な冪で消える。
方針：代数上の境界ねじれと所属が一致することを使い、有限生成性で得た指数を移す。
規約：KST §5、Stacks 0815, Theorem 38.30.7、Noether 条件は拡大環 B に課す。
使われ方：基礎環上有限でない加群にも純変換の安定性を適用する。
-/
theorem exists_pow_annihilates_boundaryTorsion_of_finite_algebra
    [IsNoetherianRing B] (f : R) :
    ∃ n : ℕ, ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_annihilates_boundaryTorsion_of_noetherian (algebraMap R B f) M
  refine ⟨n, fun m hm => ?_⟩
  have h := hn m ((mem_boundaryTorsion_algebraMap_iff (A := B) f m).mpr hm)
  simpa only [← map_pow, algebraMap_smul] using h

/--
概要：Noether 基礎環の有限型代数上有限な加群の境界ねじれは一様な冪で消える。
方針：有限型代数の Noether 性を導いて一般の代数上の消滅定理を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、有限性は B 加群としての有限性。
使われ方：一般の有限型特殊形の純変換の比較。
-/
theorem exists_pow_annihilates_boundaryTorsion_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R B] (f : R) :
    ∃ n : ℕ, ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0 := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  exact exists_pow_annihilates_boundaryTorsion_of_finite_algebra (B := B) f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
