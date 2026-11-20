module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GlobalGenericFreeCenter
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoodsTensorCancel
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0810・0811 の固定した局所中心の自由化の結論を元の基礎環と加群で述べる。
方針：中心の各実チャートで境界の正則性を確認し、二段テンソル代数と加群を取り消す。
規約：元の基礎環 A と中心の基礎環 C を別々に保持する。
使われ方：大域第二段中心の各制限中心について元の B 加群 M の自由化を述べる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：中間係数環上の固定中心の全チャートで、元の基礎環と元の加群に対する自由化基本開が存在する条件。
方針：各チャートの元の基礎環からの作用を構造写像の複合で定め、共通階数を保持する。
規約：KST §5、Stacks 0810・0811、中心は中間環 C 上、加群は元の B 上とする。
使われ方：全第二段チャートの自由化を同じ元のデータ A,B,M に統一する。
-/
def BoundaryFreeNeighborhoodsAtCenterOver (A B C : Type u) (M : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [AddCommGroup M] [Module B M] (f : C) (J : Ideal C) : Prop :=
  ∃ r : ℕ, J.FG ∧ affineCenterComplement J = PrimeSpectrum.basicOpen f ∧
    ∀ b : J,
      let E := BlowupChartRing J b
      letI : Algebra C E := (chartBaseMap J b).toAlgebra
      letI : Algebra A E := ((chartBaseMap J b).comp (algebraMap A C)).toAlgebra
      BoundaryPureFreeNeighborhoods A B E M (chartBaseMap J b f) r

/--
概要：基底変更多元環と加群に対する固定中心の自由化を、元の基礎環と元の加群に対する形へ戻せる。
方針：各チャートの境界の正則性と Noether 性から、二段テンソルの取消定理を適用する。
規約：KST §5、Stacks 0810・0811、実分裂はこの変換には不要。
使われ方：第二段の中心の各チャートで元の A と B 加群 M の一段の基底変更を扱う。
-/
theorem boundaryFreeNeighborhoodsAtCenterOver_of_baseChanged_center
    (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (f : C) (hf : IsRegular f) {J : Ideal C}
    (hJ :
      let D := C ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      BoundaryFreeNeighborhoodsAtCenter C D (D ⊗[B] M) f J) :
    BoundaryFreeNeighborhoodsAtCenterOver A B C M f J := by
  obtain ⟨r, hfg, hcomp, hfree⟩ := hJ
  refine ⟨r, hfg, hcomp, ?_⟩
  intro b
  dsimp only
  let E := BlowupChartRing J b
  let : Algebra C E := (chartBaseMap J b).toAlgebra
  let : Algebra A E := ((chartBaseMap J b).comp (algebraMap A C)).toAlgebra
  let : @IsScalarTower A C E (inferInstance : Algebra A C).toSMul
      (inferInstance : Algebra C E).toSMul (inferInstance : Algebra A E).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := C) (A := E) rfl
  let : IsNoetherianRing E := blowupChartRing_isNoetherianRing J b
  have hfE : IsRegular (chartBaseMap J b f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (chartBaseMap_nonZeroDivisors J b (isRegular_iff_mem_nonZeroDivisors.mp hf))
  exact boundaryPureFreeNeighborhoods_cancelTensorAlgebra
    A B C E M (chartBaseMap J b f) r (hfree b) hfE

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
