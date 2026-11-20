module

public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoodsGenericFree
public import SerrePositivity.AlgebraicGeometry.GenericPureFreeBaseChangeNeighborhoods

/-!
概要：KST §5、Stacks 0810・0811 の自由化基本開の追加基底変更による保存。
方針：基本開の自由性を一般点での自由性へ戻し、純変換の局所基底変更同型と自由基底の降下を使う。
規約：二段の実際の基底変更加群を保持する。
使われ方：自由化中心を細分しても基礎環を覆う自由な開部分を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：全基礎素点上で共通階数の自由化基本開を持つ純変換は、境界を正則に保つ追加基底変更後にも同じ性質を持つ。
方針：自由化基本開から全一般点での自由性を得て、基底変更した実分裂と純変換の保存補題へ渡す。
規約：KST §5、Stacks 0810・0811、元の加群の有限性は代数上に課す。
使われ方：二段構成を追加の admissible blowup で支配する際の局所自由化の保存。
-/
theorem boundaryPureFreeNeighborhoods_iterated_baseChange
    (A B C E : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra C E] [IsNoetherianRing C] [IsNoetherianRing E]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : C) (r : ℕ) (hN : BoundaryPureFreeNeighborhoods A B C M f r)
    (hf : IsRegular (algebraMap C E f)) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    BoundaryPureFreeNeighborhoods C D E (D ⊗[B] M) (algebraMap C E f) r := by
  dsimp only
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hfree := genericPureTransformFree_of_boundaryPureFreeNeighborhoods A B C M f r hN
  exact boundaryPureFreeNeighborhoods_of_genericPureTransformFree_baseChange
    C D E e' p' hs f r hfree hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
