module

public import SerrePositivity.AlgebraicGeometry.TwoStageFreeOpenPullbacks
public import SerrePositivity.AlgebraicGeometry.GlobalGenericFreeCenterDomination

/-!
概要：KST §5、Stacks 0811 の実分裂を持つ代数に対する一つの基底 blowup 上の自由化基本開の存在。
方針：二段自由化対象の全アフィン引き戻しの性質を、元の基底上の支配 blowup へ移す。
規約：実分裂は明示的な入力とし、一般の有限型加群の平坦化定理とは別に述べる。
使われ方：相対平坦化の幾何学的整な局所代数の場合の構成済みの結論。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：実分裂を持つ幾何学的整な代数上の境界外相対平坦な有限加群は、一つの基底 blowup 上で全 Noether アフィン引き戻しに自由化基本開を持つ。
方針：構成済みの二段自由化中心を一つの blowup で支配し、自由化の開局所性と前合成保存を使う。
規約：KST §5、Stacks 0811、中心は有限生成で補開集合はちょうど D(f)。
使われ方：実分裂の存在と相対 Noether 正規化による一般平坦化へ進むための実際の一段中心。
-/
theorem exists_fg_center_boundaryFreeOpenPullbacks_of_split
    {A : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] B) (hse : s.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ K : Ideal A, K.FG ∧ affineCenterComplement K = PrimeSpectrum.basicOpen f ∧
      HasBoundaryFreeOpenPullbacks B (affineBlowupπ K) f M := by
  obtain ⟨I, a, _, _, hcover, _, L, _, _, hfree, K, hKfg, hKU, g, hg⟩ :=
    exists_dominating_global_twoStage_boundaryFreeNeighborhood_center A B
      (M := M) e s hse f hf
  have h := (hasBoundaryFreeOpenPullbacks_twoStage B e s hse I a hcover L f hfree).comp g
  rw [hg] at h
  exact ⟨K, hKfg, hKU, h⟩

/--
概要：基礎環上射影的な幾何学的整な代数では、境界外相対平坦な有限加群を一つの基底 blowup 上で自由化できる。
方針：射影性から自由加群への実分裂を選び、構成済みの中心存在へ適用する。
規約：KST §5、Stacks 0811、05FS の射影性そのものはこの定理の結論に含めない。
使われ方：代数の射影性の存在定理と自由化中心の構成を接続する。
-/
theorem exists_fg_center_boundaryFreeOpenPullbacks_of_projective
    {A : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] [Algebra.FinitePresentation A B] [Module.Projective A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ K : Ideal A, K.FG ∧ affineCenterComplement K = PrimeSpectrum.basicOpen f ∧
      HasBoundaryFreeOpenPullbacks B (affineBlowupπ K) f M := by
  obtain ⟨e, he⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A B)
  exact exists_fg_center_boundaryFreeOpenPullbacks_of_split B e
    (Finsupp.linearCombination A id) he f hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
