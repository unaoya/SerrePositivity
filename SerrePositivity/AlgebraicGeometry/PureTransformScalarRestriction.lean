module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryTorsionLocalization

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の基礎環の純変換と拡大環の商としての純変換の同定。
方針：境界ねじれの制限スカラーの等式と商の線形同型を使う。
規約：加群の二つのスカラー作用はスカラー塔で両立すると仮定する。
使われ方：有限型代数上の有限加群としての純変換の有限表示性を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]

/--
概要：拡大環に関する境界ねじれの制限スカラーは基礎環に関する境界ねじれ。
方針：冪消滅の所属判定が一致することを使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、境界元は基礎環の元。
使われ方：二つの商としての純変換の実際の同型。
-/
theorem boundaryTorsion_restrictScalars (f : R) :
    (boundaryTorsion (algebraMap R B f) M).restrictScalars R = boundaryTorsion f M := by
  ext m
  exact mem_boundaryTorsion_algebraMap_iff (A := B) f m

/--
概要：基礎環の純変換と、拡大環上の商としての純変換の基礎環上の線形同型。
方針：境界ねじれの同定と商のスカラー制限の同型を合成する。
規約：KST §5、Stacks 0815, Theorem 38.30.7、拡大環上の商は元の拡大環の加群構造を保持する。
使われ方：純変換の基礎環上の平坦性と拡大環上の有限表示性を同時に扱う。
-/
def modulePureTransformScalarRestrictionEquiv (f : R) :
    modulePureTransform f M ≃ₗ[R] modulePureTransform (algebraMap R B f) M :=
  (Submodule.quotEquivOfEq _ _ (boundaryTorsion_restrictScalars (B := B) (M := M) f).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R (boundaryTorsion (algebraMap R B f) M))

/--
概要：スカラー制限による純変換の同型は元の加群の代表元を保存する。
方針：二つの商同型の代表元上の公式を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、商写像との交換式。
使われ方：代数上の純変換の計算を基礎環上の商へ戻す。
-/
theorem modulePureTransformScalarRestrictionEquiv_mk (f : R) (m : M) :
    modulePureTransformScalarRestrictionEquiv (B := B) (M := M) f (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := rfl

/--
概要：二つの純変換の表示で基礎環上の平坦性は同値。
方針：実際の線形同型による平坦性の不変性を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、平坦性を調べる環は基礎環 R。
使われ方：代数上有限な商として純変換を構成してから平坦性を論じる。
-/
theorem modulePureTransform_flat_iff_scalarRestriction (f : R) :
    Module.Flat R (modulePureTransform f M) ↔
      Module.Flat R (modulePureTransform (algebraMap R B f) M) :=
  Module.Flat.equiv_iff (modulePureTransformScalarRestrictionEquiv (B := B) (M := M) f)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
