module

public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoodCenterOver

/-!
概要：KST §5、Stacks 0811 の大域第二段中心を元の基礎環と加群のデータで自由化する。
方針：構成済みの大域中心の各制限へ、中間基底変更の取消を適用する。
規約：一般階数の一定性を仮定せず、元の A と B 加群 M を結論で保持する。
使われ方：大域第二段中心から一つの元の基礎環上の blowup への支配へ進む。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：第一段 blowup 上に一つの大域中心を選び、全第二段チャートで元の加群の一段の基底変更の自由化基本開を得る。
方針：一般階数を分離した大域第二段中心を選び、各制限中心の結論を元の基礎環と加群に戻す。
規約：KST §5、Stacks 0811, Lemma 38.30.3 の Noether・実分裂の二段構成。
使われ方：中間加群の表示に依存せずに自由化中心をさらに細分する準備。
-/
theorem exists_global_twoStage_boundaryFreeNeighborhood_center_over
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ (I : Ideal A) (a : Set.range (boundaryGenericRank A B M f) → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i k => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a k))) ∧
      ∃ L : (affineBlowup I).IdealSheafData,
        (∀ V : (affineBlowup I).affineOpens, (L.ideal V).FG) ∧
        centerComplement L = affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ∧
        ∀ i,
          let C := BlowupChartRing I (a i)
          letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
          BoundaryFreeNeighborhoodsAtCenterOver A B C M (chartBaseMap I (a i) f)
            (specIdealEquiv (.of C) (L.comap (affineBlowupChartι I (a i)))) := by
  obtain ⟨I, a, hfg, hI, hcover, hdisj, L, hLfg, hLU, hfree⟩ :=
    exists_global_twoStage_boundaryFreeNeighborhood_center A B (M := M) e p hpe f hf
  refine ⟨I, a, hfg, hI, hcover, hdisj, L, hLfg, hLU, ?_⟩
  intro i
  dsimp only
  let C := BlowupChartRing I (a i)
  let : Algebra A C := (chartBaseMap I (a i)).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (a i)
  have hfC : IsRegular (chartBaseMap I (a i) f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (chartBaseMap_nonZeroDivisors I (a i) (isRegular_iff_mem_nonZeroDivisors.mp hf))
  exact boundaryFreeNeighborhoodsAtCenterOver_of_baseChanged_center
    A B C M (chartBaseMap I (a i) f) hfC (hfree i)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
