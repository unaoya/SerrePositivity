module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangePushout
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：KST §5、Stacks 0811 の係数局所化によるテンソル代数の実際の局所化。
方針：係数変更図式が押し出しであることと局所化の基底変更の普遍条件を使う。
規約：係数変更写像は既存の明示的な写像を用い、代数構造と作用の塔を保持する。
使われ方：自由 locus と純変換を基礎環の基本開上で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：基礎係数環の局所化に沿うテンソル代数の係数変更は、元の代数上の対応する局所化である。
方針：明示的な押し出しへ Mathlib の局所化と押し出しの同値を適用する。
規約：KST §5、Stacks 0811、有限性・Noether 性・平坦性は不要。
使われ方：元の代数上の純変換の自由 locus を係数基本開から戻す。
-/
theorem tensorAlgebraBaseChange_isLocalization
    (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E]
    (S : Submonoid C) [IsLocalization S E] :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
    letI : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid D S) F := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  let : @IsScalarTower C E F (inferInstance : Algebra C E).toSMul
      (inferInstance : Algebra E F).toSMul (inferInstance : Algebra C F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := E) (A := F) rfl
  let : @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul :=
    tensorAlgebraBaseChange_isScalarTower_left_algebra A B C E
  exact (Algebra.isLocalization_iff_isPushout S E).mpr
    ((Algebra.IsPushout.comm (R := C) (S := E) (R' := D) (S' := F)).mp
      (tensorAlgebraBaseChange_isPushout A B C E))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
