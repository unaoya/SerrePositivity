module

public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoodsBasic
public import SerrePositivity.AlgebraicGeometry.GenericPureFreePushout

/-!
概要：KST §5、Stacks 0810・0811 の相対自由化基本開の押し出しによる保存。
方針：元の自由化基本開を一般点での自由性へ戻し、任意の押し出し実現での保存を適用する。
規約：実際の代数と基底変更加群で同じ共通階数を保持する。
使われ方：構成済みの自由化中心を基底変更の表示に依存せず細分へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：共通階数の自由化基本開を持つ純変換は、正則な境界を保つ押し出しの任意の実現で同じ性質を持つ。
方針：一般点での自由性との同値を使い、縮約一般点と局所純変換の比較に基づく押し出し保存へ渡す。
規約：KST §5、Stacks 0810・0811、実分裂と両代数の幾何学的条件を明示する。
使われ方：元の基礎環上の一つの blowup による共通支配へ自由化基本開を移す準備。
-/
theorem relativePureFreeNeighborhoods_pushout
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A C B D]
    [IsNoetherianRing A] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [Module.Flat C D] [Algebra.FinitePresentation C D]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (r : ℕ) (hN : RelativePureFreeNeighborhoods A B M f r)
    (hf : IsRegular (algebraMap A C f)) :
    RelativePureFreeNeighborhoods C D (D ⊗[B] M) (algebraMap A C f) r := by
  have hfree := (relativePureFreeNeighborhoods_iff_genericPureFree A B M f r).mp hN
  exact relativePureFreeNeighborhoods_of_genericPureTransformFree_pushout
    A B C D e p hpe f r hfree hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
