module

public import SerrePositivity.AlgebraicGeometry.GenericPureFreeBaseChange
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoods

/-!
概要：KST §5、Stacks 0810・0811 の追加基底変更後の一般点を含む自由化基本開。
方針：一般点自由性と階数の保存から、有限表示性により自由基底を基本開へ降ろす。
規約：追加係数環で境界元は正則とし、係数変更の平坦性は仮定しない。
使われ方：共通細分後に共通階数の自由な開部分で基礎環を覆う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：一般点で自由な純変換は追加の基底変更後にも各基礎素点上の同じ階数の自由化基本開を持つ。
方針：一般点での自由性と階数の基底変更保存を、自由基底の基本開への降下へ接続する。
規約：KST §5、Stacks 0810・0811、実分裂と Noether 係数環を入力する。
使われ方：元の自由化中心を追加の admissible blowup で細分する準備。
-/
theorem boundaryPureFreeNeighborhoods_of_genericPureTransformFree_baseChange
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (r : ℕ)
    (hfree : ∀ P : PrimeSpectrum A,
      let Q := geometricallyIntegralGenericPrime A B P
      Q ∈ Module.freeLocus B (modulePureTransform (algebraMap A B f) M) ∧
        Module.rankAtStalk (modulePureTransform (algebraMap A B f) M) Q = r)
    (hf : IsRegular (algebraMap A C f)) :
    BoundaryPureFreeNeighborhoods A B C M (algebraMap A C f) r := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let G := modulePureTransform (algebraMap C D (algebraMap A C f)) (D ⊗[B] M)
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing C D
  let : Module.FinitePresentation D G := Module.finitePresentation_of_finite D G
  intro P
  have hQ := genericPureTransformFree_baseChange A B C e p hpe f r hfree hf P
  obtain ⟨g, hg, hfg, hr⟩ := exists_away_free_finrank_of_mem_freeLocus
    (geometricallyIntegralGenericPrime C D P) hQ.1
  exact ⟨g, hg, hfg, hr.trans hQ.2⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
