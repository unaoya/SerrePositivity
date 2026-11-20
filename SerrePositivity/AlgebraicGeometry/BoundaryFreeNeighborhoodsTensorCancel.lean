module

public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoodsAlgEquiv
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangePushout

/-!
概要：KST §5、Stacks 0810・0811 の二段テンソル代数の自由化基本開を元の基礎環の表示へ戻す。
方針：取消代数同型で自由化を移し、実際の作用の塔で加群のテンソルを二回取り消す。
規約：実分裂は不要で、最後の係数環に Noether 性と境界正則性を課す。
使われ方：第一段チャート上で構成した第二段の自由化中心を元の加群について読む。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：中間基礎環と基底変更加群に対する自由化基本開を、元の基礎環と元の加群の一段の表示へ戻せる。
方針：二段テンソルの取消代数同型で純変換の自由化を移し、二つの加群の取消同型を適用する。
規約：KST §5、Stacks 0810・0811、最後の係数環は Noether、そこで境界元は正則。
使われ方：二段中心の局所自由化の結論を元の A と B 加群 M について統一する。
-/
theorem boundaryPureFreeNeighborhoods_cancelTensorAlgebra
    (A B C E : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E]
    [IsNoetherianRing E] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (f : E) (r : ℕ)
    (hN :
      let D := C ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      BoundaryPureFreeNeighborhoods C D E (D ⊗[B] M) f r)
    (hf : IsRegular f) : BoundaryPureFreeNeighborhoods A B E M f r := by
  let D := C ⊗[A] B
  let S := E ⊗[C] D
  let T := E ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra D S := Algebra.TensorProduct.rightAlgebra
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra D T := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  let K : S ≃ₐ[E] T := Algebra.TensorProduct.cancelBaseChange A C E E B
  let : Algebra S T := K.toRingHom.toAlgebra
  let : IsScalarTower D S T := by
    apply IsScalarTower.of_algebraMap_eq' (R := D) (S := S) (A := T)
    exact (tensorAlgebraBaseChange_cancel_includeRight A B C E).symm
  let : IsScalarTower B D T := tensorAlgebraBaseChange_isScalarTower_right A B C E
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E S))) :=
    geometricallyIntegral_tensorProjection C D E
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E T))) :=
    geometricallyIntegral_tensorProjection A B E
  have hsource : RelativePureFreeNeighborhoods E S (S ⊗[D] (D ⊗[B] M)) f r :=
    (boundaryPureFreeNeighborhoods_iff_relative C D E (D ⊗[B] M) f r).mp hN
  have hreg : IsRegular (algebraMap E T f) := algebraMap_isRegular_of_flat E T f hf
  have h := relativePureFreeNeighborhoods_baseChange_of_algEquiv
    E S T (S ⊗[D] (D ⊗[B] M)) K f r hsource hreg
  have hmid : RelativePureFreeNeighborhoods E T (T ⊗[D] (D ⊗[B] M)) f r := h.cancelBaseChange
  have hfinal : RelativePureFreeNeighborhoods E T (T ⊗[B] M) f r := hmid.cancelBaseChange
  exact (boundaryPureFreeNeighborhoods_iff_relative A B E M f r).mpr hfinal

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
