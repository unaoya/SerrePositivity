module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：KST §5、Stacks 0815 の純変換の線形同型と境界表示の変更に対する不変性。
方針：線形同型が境界ねじれを互いに保つことから商の同型を作る。
規約：境界元を変更する場合は環内での実際の等式を使う。
使われ方：二段の基底変更のテンソル同型で純変換を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/--
概要：線形同型は境界ねじれ部分加群を同定する。
方針：写像と逆写像が冪消滅を保つことを使う。
規約：KST §5、Stacks 0815、同じ境界元を使う。
使われ方：純変換の商の間の同型の構成。
-/
theorem boundaryTorsion_map_equiv (f : R) (e : M ≃ₗ[R] N) :
    (boundaryTorsion f M).map e.toLinearMap = boundaryTorsion f N := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr (boundaryTorsion_map_le f e.toLinearMap)
  · intro n hn
    exact ⟨e.symm n, boundaryTorsion_map_le f e.symm.toLinearMap hn, e.apply_symm_apply n⟩

/--
概要：線形同型は純変換の実際の線形同型を誘導する。
方針：境界ねじれの像の等式で商の同型を作る。
規約：KST §5、Stacks 0815、係数環上線形な同型を入力する。
使われ方：テンソル積の打ち消し同型による純変換の比較。
-/
def modulePureTransformCongr (f : R) (e : M ≃ₗ[R] N) :
    modulePureTransform f M ≃ₗ[R] modulePureTransform f N :=
  Submodule.Quotient.equiv _ _ e (boundaryTorsion_map_equiv f e)

/--
概要：環内で等しい境界元による純変換は線形同型。
方針：境界の等式に沿って恒等同型を移す。
規約：KST §5、Stacks 0815、局所化のスカラー塔で得られる等式を使う。
使われ方：二段の係数写像の境界の像の照合。
-/
def modulePureTransformBoundaryCongr (M : Type*) [AddCommGroup M] [Module R M]
    {f g : R} (h : f = g) : modulePureTransform f M ≃ₗ[R] modulePureTransform g M := by
  subst g
  exact LinearEquiv.refl R _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
