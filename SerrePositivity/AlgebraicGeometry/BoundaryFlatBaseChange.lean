module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeFlat
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：KST §5、Stacks 0810・0811 の境界外の相対平坦性の任意の基底変更。
方針：境界を可逆化した環間の写像を選び、平坦加群の基底変更とテンソル取消を使う。
規約：係数環の平坦性は要求しない。
使われ方：階数を分離した実チャートに一定一般階数の中心の定理を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
  (M : Type*) [AddCommGroup M] [Module R M]

/--
概要：境界外で平坦な加群は任意の基底変更後も境界外で平坦。
方針：境界局所化環間の自然な準同型を使い、基底変更した平坦加群の二段テンソルを取り消す。
規約：KST §5、Stacks 0810・0811、元の加群の全体での平坦性は不要。
使われ方：blowup チャートに移った加群の境界外の平坦性。
-/
theorem flat_tensor_away_of_boundary_flat (f : R)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[R] M)] :
    Module.Flat (Localization.Away (algebraMap R C f))
      ((Localization.Away (algebraMap R C f)) ⊗[R] M) := by
  let F := Localization.Away f
  let L := Localization.Away (algebraMap R C f)
  let : Algebra F L := (Localization.awayMap (algebraMap R C) f).toAlgebra
  let : IsScalarTower R F L := by
    apply IsScalarTower.of_algebraMap_eq' (R := R) (S := F) (A := L)
    ext r
    change algebraMap C L (algebraMap R C r) =
      (Localization.awayMap (algebraMap R C) f) (algebraMap R F r)
    exact (IsLocalization.map_eq (M := Submonoid.powers f) (S := F)
      (T := Submonoid.powers (algebraMap R C f)) (Q := L) (g := algebraMap R C)
      (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) r).symm
  let : Module.Flat L (L ⊗[F] (F ⊗[R] M)) := inferInstance
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R F L L M).symm

/--
概要：代数上の加群の基底変更も、境界を可逆化すると基礎環上平坦となる。
方針：テンソル代数の取消同型を境界局所化へ基底変更し、二段テンソルを取り消す。
規約：KST §5、Stacks 0810・0811、元の代数や係数環の平坦性は不要。
使われ方：実際の blowup チャート上の加群に境界外の平坦性を与える。
-/
theorem flat_tensorAlgebra_away_of_boundary_flat (B : Type*) [CommRing B] [Algebra R B]
    [Module B M] [IsScalarTower R B M] (f : R)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[R] M)] :
    let D := C ⊗[R] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    Module.Flat (Localization.Away (algebraMap R C f))
      ((Localization.Away (algebraMap R C f)) ⊗[C] (D ⊗[B] M)) := by
  let D := C ⊗[R] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let L := Localization.Away (algebraMap R C f)
  let : Module.Flat L (L ⊗[R] M) := flat_tensor_away_of_boundary_flat R C M f
  let E : (L ⊗[C] (D ⊗[B] M)) ≃ₗ[L] (L ⊗[R] M) :=
    ((tensorAlgebraBaseChangeEquiv R B C M).baseChange C L _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R C L L M)
  exact Module.Flat.of_linearEquiv E

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
