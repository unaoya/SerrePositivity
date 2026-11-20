module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks

/-!
概要：KST §5、Stacks 0815 の Noether アフィンモデルの平坦性から全アフィン引き戻しの平坦性を導く。
方針：Spec の反変合成と追加基底変更の安定性を組み合わせる。
規約：境界の像が正則となる試験対象を扱う。
使われ方：局所平坦化した blowup の標準チャートを開被覆で貼り合わせる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：Noether アフィン環上の純変換が平坦なら、その Spec 上では正則な境界を持つ全引き戻しでも平坦。
方針：試験射を環準同型へ戻し、係数環の追加基底変更の平坦性保存を使う。
規約：KST §5、Stacks 0815、元の加群は基礎環上有限。
使われ方：実際のチャート上の平坦性をスキーム射の引き戻しの性質へ接続する。
-/
theorem hasFlatPurePullbacks_spec {R A : CommRingCat.{u}} [IsNoetherianRing A]
    (φ : R ⟶ A) (f : R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hflat : letI : Algebra R A := φ.hom.toAlgebra
      Module.Flat A (modulePureTransform (φ.hom f) (A ⊗[R] M))) :
    HasFlatPurePullbacks (Spec.map φ) f M := by
  intro B j
  let P (ψ : R →+* B) : Prop :=
    letI : Algebra R B := ψ.toAlgebra
    IsRegular (ψ f) → Module.Flat B (modulePureTransform (ψ f) (B ⊗[R] M))
  have hcomp : P ((Spec.preimage j).hom.comp φ.hom) := by
    let : Algebra R A := φ.hom.toAlgebra
    let : Algebra A B := (Spec.preimage j).hom.toAlgebra
    let : Algebra R B := ((Spec.preimage j).hom.comp φ.hom).toAlgebra
    have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : Module.Flat A (modulePureTransform (φ.hom f) (A ⊗[R] M)) := hflat
    intro hf
    exact tensorPureTransform_flat_baseChange R A B M f hf
  exact (congrArg P (pureTransformCoefficientMap_spec φ j)).mpr hcomp

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
