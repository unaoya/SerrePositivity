module

public import SerrePositivity.AlgebraicGeometry.BoundaryGenericRankBaseChange
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals

/-!
概要：KST §5、Stacks 0811 の実チャート上の加群の境界外一般階数の一定化。
方針：元の階数関数の開閉部分を分離する中心に、境界外一般階数の基底変更公式を接続する。
規約：通常の Rees Proj の実際の標準チャートと基底変更加群を使う。
使われ方：一般階数一定の係数中心の定理を有限個の実チャート上で適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外で相対平坦な有限加群の実際の境界外一般階数を、有限標準チャートごとに一定にする中心が存在する。
方針：階数の開閉分割を分離する実中心を選び、各チャート上の加群の階数を引き戻し公式で照合する。
規約：KST §5、Stacks 0811, Lemma 38.30.3、実分裂を明示的に入力する。
使われ方：一定一般階数の自由化中心の存在定理への有限チャート還元。
-/
theorem exists_fg_center_constant_actual_boundaryGenericRank
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
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      ∀ i,
        let C := BlowupChartRing I (a i)
        letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
        letI : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (a i)
        let D := C ⊗[A] B
        letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
        letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
          geometricallyIntegral_tensorProjection A B C
        ∀ P : PrimeSpectrum (Localization.Away (chartBaseMap I (a i) f)),
          boundaryGenericRank C D (D ⊗[B] M) (chartBaseMap I (a i) f) P = i.val := by
  obtain ⟨I, a, hfg, hI, hcover, hdisj, hconst⟩ :=
    exists_fg_center_constant_boundaryGenericRank A B M e p hpe f hf
  refine ⟨I, a, hfg, hI, hcover, hdisj, ?_⟩
  intro i
  dsimp only
  let C := BlowupChartRing I (a i)
  let : Algebra A C := (chartBaseMap I (a i)).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (a i)
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  intro P
  change boundaryGenericRank C D (D ⊗[B] M) (algebraMap A C f) P = i.val
  rw [boundaryGenericRank_baseChange A B C e p hpe f P]
  exact hconst i P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
