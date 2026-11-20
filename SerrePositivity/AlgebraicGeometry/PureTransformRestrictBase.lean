module

public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks

/-!
概要：KST §5、Stacks 0815 のチャート環を基礎環とした純変換の平坦性を元の基礎環へ戻す。
方針：二段のテンソル積の純変換の打ち消し同型を全アフィン試験対象で使う。
規約：基礎環の射を CommRingCat の実際の射として指定する。
使われ方：二段目の局所平坦化を一段目の構造射と合成する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：中間環上の純変換の引き戻し平坦性は元の環上の加群についての引き戻し平坦性を与える。
方針：係数写像の合成式と二段の純変換の打ち消しを使う。
規約：KST §5、Stacks 0815、元の加群の中間環への基底変更を入力する。
使われ方：局所平坦化の結論を元の基礎環について表す。
-/
theorem HasFlatPurePullbacks.restrictBase {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (φ : R ⟶ A) (p : X ⟶ Spec A) (f : R) (M : Type v) [AddCommGroup M] [Module R M]
    (hp : letI : Algebra R A := φ.hom.toAlgebra
      HasFlatPurePullbacks p (φ.hom f) (A ⊗[R] M)) :
    HasFlatPurePullbacks (p ≫ Spec.map φ) f M := by
  intro B j
  let P (ψ : R →+* B) : Prop :=
    letI : Algebra R B := ψ.toAlgebra
    IsRegular (ψ f) → Module.Flat B (modulePureTransform (ψ f) (B ⊗[R] M))
  let θ := pureTransformCoefficientMap p j
  have hcomp : P (θ.comp φ.hom) := by
    let : Algebra R A := φ.hom.toAlgebra
    let : Algebra A B := θ.toAlgebra
    let : Algebra R B := (θ.comp φ.hom).toAlgebra
    have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    intro hf
    have : Module.Flat B (modulePureTransform (θ (φ.hom f)) (B ⊗[A] (A ⊗[R] M))) := hp B j hf
    exact tensorPureTransform_flat_cancelBaseChange R A B M f
  exact (congrArg P (pureTransformCoefficientMap_post_spec p φ j)).mpr hcomp

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
