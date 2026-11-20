module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GlobalGenericFreeCenterOver
public import SerrePositivity.AlgebraicGeometry.ExactAffineAdmissibleComposition

/-!
概要：KST §5、Stacks 080Y・0811 の二段の一般点自由化中心を元の基底の一つの blowup で支配する。
方針：構成済みの大域第二段中心へ、中心外を揃えた合成支配を適用する。
規約：第二段の対象と各チャートの自由化のデータを保持し、実際の支配射を返す。
使われ方：正則境界を保つ追加の基底変更で自由化を保存するための幾何学的入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：実分裂と境界外平坦性から構成した二段自由化中心を、元の基底上の一つの有限生成中心の blowup で支配できる。
方針：一般階数の分離と大域第二段中心を選び、既証の合成支配の中心へ (f) を掛ける。
規約：KST §5、Stacks 080Y・0811、元の加群を全第二段チャートの結論に保持する。
使われ方：自由化基本開の支配射による引き戻しに必要な実際の射と可換式を与える。
-/
theorem exists_dominating_global_twoStage_boundaryFreeNeighborhood_center
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
        (∀ i,
          let C := BlowupChartRing I (a i)
          letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
          BoundaryFreeNeighborhoodsAtCenterOver A B C M (chartBaseMap I (a i) f)
            (specIdealEquiv (.of C) (L.comap (affineBlowupChartι I (a i))))) ∧
        ∃ K : Ideal A, K.FG ∧ affineCenterComplement K = PrimeSpectrum.basicOpen f ∧
          ∃ g : affineBlowup K ⟶ blowup L,
            g ≫ blowupπ L ≫ affineBlowupπ I = affineBlowupπ K := by
  obtain ⟨I, a, hfg, hI, hcover, hdisj, L, hLfg, hLU, hfree⟩ :=
    exists_global_twoStage_boundaryFreeNeighborhood_center_over A B (M := M) e p hpe f hf
  refine ⟨I, a, hfg, hI, hcover, hdisj, L, hLfg, hLU, hfree, ?_⟩
  exact exists_affine_exact_admissible_composition_domination I L f
    (le_of_eq hI.symm) (le_of_eq hLU.symm)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
