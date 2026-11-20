module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：KST §5、Stacks 0815 の一様に消える境界ねじれから純変換の冪倍の戻し写像を作る。
方針：元の加群のスカラー倍写像をねじれによる商へ降ろす。
規約：指数 n はねじれ全体を消すものを明示する。
使われ方：平坦な純変換の追加の基底変更に対する安定性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R) (M : Type*) [AddCommGroup M] [Module R M]
  (n : ℕ) (hn : ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0)

/--
概要：純変換から元の加群へ戻す境界の冪倍の線形写像。
方針：冪倍写像の核が境界ねじれを含むことを使い商へ降ろす。
規約：KST §5、Stacks 0815、通常の商写像の逆元とは主張しない。
使われ方：追加の基底変更後の核の冪消滅。
-/
def boundaryPowerLift : modulePureTransform f M →ₗ[R] M :=
  (boundaryTorsion f M).liftQ (f ^ n • LinearMap.id) (by
    intro m hm
    exact hn m hm)

/--
概要：冪倍の戻し写像と商写像の合成は元の加群の冪倍写像。
方針：商の代表元上で定義を使う。
規約：KST §5、Stacks 0815、冪はねじれを消す指数。
使われ方：基底変更後の核を同じ冪で消す証明。
-/
theorem boundaryPowerLift_comp_mkQ :
    (boundaryPowerLift f M n hn).comp (boundaryTorsion f M).mkQ =
      f ^ n • LinearMap.id := by
  ext m
  rfl

/--
概要：商写像と冪倍の戻し写像の合成は純変換上の冪倍写像。
方針：商写像の全射性で代表元へ戻す。
規約：KST §5、Stacks 0815、元の加群上の等式と同じ指数を使う。
使われ方：元の加群と純変換の間の冪倍同型の照合。
-/
theorem mkQ_comp_boundaryPowerLift :
    (boundaryTorsion f M).mkQ.comp (boundaryPowerLift f M n hn) =
      f ^ n • LinearMap.id := by
  ext m
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
