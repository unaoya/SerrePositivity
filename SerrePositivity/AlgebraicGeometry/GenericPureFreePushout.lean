module

public import SerrePositivity.AlgebraicGeometry.GenericPrimePushout
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange
public import SerrePositivity.AlgebraicGeometry.GenericBoundaryFreeNeighborhood
public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoods

/-!
概要：KST §5、Stacks 0810・0811 の押し出しの任意の実現での一般点自由性の保存。
方針：拡大一般点の縮約を照合し、純変換の一素点での基底変更保存と自由基底の降下を使う。
規約：実際の代数とその基底変更加群に直接結論を述べる。
使われ方：二段テンソル積を別の実現に置き換えて自由化基本開を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
  [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A C B D]
  [IsNoetherianRing A] [IsNoetherianRing C]
  [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  [Module.Flat C D] [Algebra.FinitePresentation C D]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D)))]
  {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
  (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
  (f : A) (r : ℕ)
  (hfree : ∀ P : PrimeSpectrum A,
    let Q := geometricallyIntegralGenericPrime A B P
    Q ∈ Module.freeLocus B (modulePureTransform (algebraMap A B f) M) ∧
      Module.rankAtStalk (modulePureTransform (algebraMap A B f) M) Q = r)
  (hf : IsRegular (algebraMap A C f))

include e p hpe hfree hf

/--
概要：一般点で自由な純変換は、押し出しの任意の実現への基底変更後にも同じ階数で一般点で自由。
方針：押し出しでの縮約一般点の比較と平坦代数での境界正則性を一素点の保存補題へ渡す。
規約：KST §5、Stacks 0810・0811、両側の幾何学的整性と実分裂を明示する。
使われ方：テンソル積の括弧や基底変更表示を変えた後の純変換を照合する。
-/
theorem genericPureTransformFree_pushout (P : PrimeSpectrum C) :
    let Q := geometricallyIntegralGenericPrime C D P
    let G := modulePureTransform (algebraMap C D (algebraMap A C f)) (D ⊗[B] M)
    Q ∈ Module.freeLocus D G ∧ Module.rankAtStalk G Q = r := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let Q := geometricallyIntegralGenericPrime C D P
  let L := Localization.AtPrime Q.asIdeal
  have hQ := geometricallyIntegralGenericPrime_pushout_comap A B C D e p hpe P
  have hsource : Q.comap (algebraMap B D) ∈
      Module.freeLocus B (modulePureTransform (algebraMap A B f) M) ∧
      Module.rankAtStalk (modulePureTransform (algebraMap A B f) M)
        (Q.comap (algebraMap B D)) = r := by
    rw [hQ]
    exact hfree _
  have hscalar : algebraMap B D (algebraMap A B f) =
      algebraMap C D (algebraMap A C f) := by
    rw [← IsScalarTower.algebraMap_apply A B D, IsScalarTower.algebraMap_apply A C D]
  have hd : IsRegular (algebraMap D L (algebraMap B D (algebraMap A B f))) := by
    rw [hscalar]
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (S := L) Q.asIdeal.primeCompl
      (isRegular_iff_mem_nonZeroDivisors.mp
        (algebraMap_isRegular_of_flat C D (algebraMap A C f) hf))
  have h := pureTransform_freeLocus_rankAtStalk_baseChange
    (M := M) (algebraMap A B f) r Q hsource hd
  rwa [hscalar] at h

/--
概要：一般点で自由な純変換は、押し出しの任意の実現で基礎環を覆う同じ階数の自由化基本開を持つ。
方針：全一般点での自由性と階数の保存から、有限表示加群の自由基底を基本開へ降ろす。
規約：KST §5、Stacks 0810・0811、新しい代数と加群の実際の表示に結論を述べる。
使われ方：自由化中心の構成を一つの元の基礎環上の blowup へ移す準備。
-/
theorem relativePureFreeNeighborhoods_of_genericPureTransformFree_pushout :
    RelativePureFreeNeighborhoods C D (D ⊗[B] M) (algebraMap A C f) r := by
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing C D
  let G := modulePureTransform (algebraMap C D (algebraMap A C f)) (D ⊗[B] M)
  let : Module.FinitePresentation D G := Module.finitePresentation_of_finite D G
  intro P
  have hQ := genericPureTransformFree_pushout A B C D e p hpe f r hfree hf P
  obtain ⟨g, hg, hfg, hr⟩ := exists_away_free_finrank_of_mem_freeLocus
    (geometricallyIntegralGenericPrime C D P) hQ.1
  exact ⟨g, hg, hfg, hr.trans hQ.2⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
