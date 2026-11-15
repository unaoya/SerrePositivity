module

public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition

/-!
概要：実際の tensor 模型に沿って affine v 被覆を移す。
方針：指定された代数同型の Cartesian 比較と、付値判定の底変換を用いる。
規約：係数射の平坦性・忠実性を仮定しない。
使われ方：B03・B04 の各係数段の被覆性を保つ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 実際の tensor 模型に移した affine v 被覆は、同じ付値判定を満たす。 -/
theorem isSchemeVCover_affineTensorModel
    {A R S C : Type u} [CommRing A] [CommRing R] [CommRing S] [CommRing C]
    [Algebra A R] [Algebra A S] [Algebra R C] (e : R ⊗[A] S ≃ₐ[R] C)
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap A S)))) :
    IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R C))) :=
  IsSchemeVCover.baseChange (isPullback_affineTensorModel e) hf

end SerrePositivity.AlgebraicGeometry
