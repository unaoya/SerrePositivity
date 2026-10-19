module

public import SerrePositivity.KST.Spectra.WeightCylinderFunctor
public import SerrePositivity.KST.Spectra.ReedyWeightCofibrancy

/-!
概要：Reedy Kan 置換した終頂点の射に、実際の図式ホモトピー逆を作る。
方針：二射影の切断と、Reedy cofibrant な中間重みの境界 cylinder の垂直充填を組み合わせる。
規約：ホモトピーは全余単体次数で自然な cylinder の射である。
使われ方：Goerss–Jardine VII §4。重みの比較を end に移す入力。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 置換した終頂点の射の、二射影と切断から作る実際の逆射。 -/
def kanWeightInverse : CosimplicialKanReplacement.functor.obj stdSimplex.{u} ⟶
    CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u} :=
  ReedyWeightCofibrancy.targetSection ≫ CosimplicialTwoProjections.sourceProjection kanWeightMap

/-- 実際の逆射との両合成を恒等へ結ぶ、自然な二つの図式 cylinder。 -/
lemma kanWeightMap_homotopyInverse :
    ∃ H : WeightTensorLatching.diagram
        (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u})
        (Δ[1] : SSet.{u}) ⟶
        CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u},
      (∀ j, SSet.ι₀ ≫ H.app j = (kanWeightMap ≫ kanWeightInverse).app j) ∧
      (∀ j, SSet.ι₁ ≫ H.app j = 𝟙 _) ∧
      ∃ K : WeightTensorLatching.diagram
          (CosimplicialKanReplacement.functor.obj stdSimplex.{u}) (Δ[1] : SSet.{u}) ⟶
          CosimplicialKanReplacement.functor.obj stdSimplex.{u},
        (∀ j, SSet.ι₀ ≫ K.app j = (kanWeightInverse ≫ kanWeightMap).app j) ∧
        (∀ j, SSet.ι₁ ≫ K.app j = 𝟙 _) := by
  let a := CosimplicialTwoProjections.inclusion kanWeightMap.{u}
  let p := CosimplicialTwoProjections.sourceProjection kanWeightMap.{u}
  let q := CosimplicialTwoProjections.targetProjection kanWeightMap.{u}
  let s := ReedyWeightCofibrancy.targetSection.{u}
  have hap : a ≫ p = 𝟙 _ := CosimplicialTwoProjections.inclusion_sourceProjection _
  have haq : a ≫ q = kanWeightMap := CosimplicialTwoProjections.inclusion_targetProjection _
  have hsq : s ≫ q = 𝟙 _ := ReedyWeightCofibrancy.targetSection_projection
  obtain ⟨U, hu₀, hu₁, _⟩ := WeightCylinderLifting.exists_vertical_homotopy
    ReedyWeightCofibrancy.twoProjections p kanWeightSourceProjection_matching
    (p ≫ a) (𝟙 _) (by rw [Category.assoc, hap, Category.comp_id, Category.id_comp])
  obtain ⟨V, hv₀, hv₁, _⟩ := WeightCylinderLifting.exists_vertical_homotopy
    ReedyWeightCofibrancy.twoProjections q kanWeightTargetProjection_matching
    (q ≫ s) (𝟙 _) (by rw [Category.assoc, hsq, Category.comp_id, Category.id_comp])
  refine ⟨WeightCylinderFunctor.map a (Δ[1] : SSet.{u}) ≫ V ≫ p, ?_, ?_,
    WeightCylinderFunctor.map s (Δ[1] : SSet.{u}) ≫ U ≫ q, ?_, ?_⟩
  · intro j
    have h := WeightCylinderFunctor.zero_composite a V p (q ≫ s) hv₀ j
    have he : a ≫ (q ≫ s) ≫ p = kanWeightMap ≫ kanWeightInverse := by
      rw [← Category.assoc, ← Category.assoc, haq]
      rfl
    rw [he] at h
    exact h
  · intro j
    have h := WeightCylinderFunctor.one_composite a V p (𝟙 _) hv₁ j
    simpa only [Category.id_comp, hap, NatTrans.id_app] using h
  · intro j
    have h := WeightCylinderFunctor.zero_composite s U q (p ≫ a) hu₀ j
    have he : s ≫ (p ≫ a) ≫ q = kanWeightInverse ≫ kanWeightMap := by
      simp only [Category.assoc]
      rw [haq]
      rfl
    rw [he] at h
    exact h
  · intro j
    have h := WeightCylinderFunctor.one_composite s U q (𝟙 _) hu₁ j
    simpa only [Category.id_comp, hsq, NatTrans.id_app] using h

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
