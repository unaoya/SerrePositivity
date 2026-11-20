module

public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.FiniteTypeTensorPureTransformBaseChange

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の有限型代数上有限な加群のアフィン引き戻し平坦性。
方針：基底変更代数上の有限性を使う追加基底変更の安定性を Spec の試験射に適用する。
規約：元の加群の基礎環上の有限性は仮定しない。
使われ方：一般の有限型特殊形で局所平坦化を大域化する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：Noether アフィンモデルで平坦な純変換は、有限型代数上有限な加群でも全アフィン引き戻しで平坦。
方針：試験射の係数写像を照合し、基底変更代数上の有限性による安定性を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、有限性は B 加群としてのもの。
使われ方：有限型の一般形のチャート平坦性とスキーム上の局所性の接続。
-/
theorem hasFlatPurePullbacks_spec_of_finiteTypeModule
    {R A : CommRingCat.{u}} [IsNoetherianRing A] (B : Type w) [CommRing B] [Algebra R B]
    (φ : R ⟶ A) (f : R) (M : Type v) [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Algebra.FiniteType R B] [Module.Finite B M]
    (hflat : letI : Algebra R A := φ.hom.toAlgebra
      Module.Flat A (modulePureTransform (φ.hom f) (A ⊗[R] M))) :
    HasFlatPurePullbacks (Spec.map φ) f M := by
  intro C j
  let P (ψ : R →+* C) : Prop :=
    letI : Algebra R C := ψ.toAlgebra
    IsRegular (ψ f) → Module.Flat C (modulePureTransform (ψ f) (C ⊗[R] M))
  have hcomp : P ((Spec.preimage j).hom.comp φ.hom) := by
    let : Algebra R A := φ.hom.toAlgebra
    let : Algebra A C := (Spec.preimage j).hom.toAlgebra
    let : Algebra R C := ((Spec.preimage j).hom.comp φ.hom).toAlgebra
    have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : Module.Flat A (modulePureTransform (φ.hom f) (A ⊗[R] M)) := hflat
    intro hf
    exact finiteType_tensorPureTransform_flat_baseChange R B A C M f hf
  exact (congrArg P (pureTransformCoefficientMap_spec φ j)).mpr hcomp

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
