module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangePushout
public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoodsPushout

/-!
概要：KST §5、Stacks 0810・0811 の自由化基本開の追加基底変更を一段の標準表示で保存する。
方針：テンソル代数の実際の押し出しを使い、相対自由化の保存と加群の取消同型を合成する。
規約：結論の代数と加群は元の基礎環からの一段の基底変更とする。
使われ方：二段の自由化中心を元の基礎環上の一つの blowup で支配する準備。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：自由化基本開の存在は追加の正則境界基底変更で保たれ、元の基礎環上の一段の表示に戻せる。
方針：中間テンソル代数からの押し出し保存を適用し、元の代数上の加群の二段テンソルを取り消す。
規約：KST §5、Stacks 0810・0811、実分裂を入力し、Noether 条件は二つの係数環に課す。
使われ方：細分後の純変換の自由化基本開を元の加群の一段の基底変更について述べる。
-/
theorem boundaryPureFreeNeighborhoods_baseChange
    (A B C E : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E]
    [IsNoetherianRing C] [IsNoetherianRing E]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : C) (r : ℕ) (hN : BoundaryPureFreeNeighborhoods A B C M f r)
    (hf : IsRegular (algebraMap C E f)) :
    BoundaryPureFreeNeighborhoods A B E M (algebraMap C E f) r := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B F := Algebra.TensorProduct.rightAlgebra
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  let : @IsScalarTower C E F (inferInstance : Algebra C E).toSMul
      (inferInstance : Algebra E F).toSMul (inferInstance : Algebra C F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := E) (A := F) rfl
  let : @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul :=
    tensorAlgebraBaseChange_isScalarTower_left_algebra A B C E
  let : IsScalarTower B D F := tensorAlgebraBaseChange_isScalarTower_right A B C E
  let : Algebra.IsPushout C E D F := tensorAlgebraBaseChange_isPushout A B C E
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
    geometricallyIntegral_tensorProjection A B E
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hsource : RelativePureFreeNeighborhoods C D (D ⊗[B] M) f r :=
    (boundaryPureFreeNeighborhoods_iff_relative A B C M f r).mp hN
  have h := relativePureFreeNeighborhoods_pushout C D E F e' p' hs f r hsource hf
  have hfinal : RelativePureFreeNeighborhoods E F (F ⊗[B] M) (algebraMap C E f) r :=
    h.cancelBaseChange
  exact (boundaryPureFreeNeighborhoods_iff_relative A B E M (algebraMap C E f) r).mpr hfinal

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
