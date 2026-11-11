module

public import SerrePositivity.KST.Spectra.PointedCochainDensity
public import SerrePositivity.KST.Spectra.CochainDensityCoefficient

/-!
概要：点つき通常の Tot と点つき end の密度比較の係数への自然性。
方針：忘却の二つの比較の自然性と通常の密度の自然性を合成する。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。hG と通常の Tot の射の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき密度の同型は係数の自然変換に自然。
方針：通常の密度の同型の自然性を cochain と end の忘却比較で共役する。
規約：任意の係数図式で成立する通常の点つき射の可換式。
使われ方：Goerss–Jardine VIII §§1–2。群作用の射と Tot の射の整合性。 -/
lemma pointedTotalizationEndIso_natural {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
    {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    PointedTotalization.map (weightedCochainsMap (discreteLevels W) τ) ≫
        (pointedTotalizationEndIso W E).hom =
      (pointedTotalizationEndIso W D).hom ≫ PointedWeightedEnd.map W τ := by
  let C := discreteLevels W
  let φD := UnderlyingWeightedCochains.pointedUnderlyingIso C D
  let φE := UnderlyingWeightedCochains.pointedUnderlyingIso C E
  let δD := totalizationEndIso W (D ⋙ PointedSimplicialSet.forget)
  let δE := totalizationEndIso W (E ⋙ PointedSimplicialSet.forget)
  let εD := PointedWeightedEnd.underlyingIso W D
  let εE := PointedWeightedEnd.underlyingIso W E
  let c := Functor.whiskerRight (weightedCochainsMap C τ) PointedSimplicialSet.forget
  let t := Functor.whiskerRight τ PointedSimplicialSet.forget
  have hφ := congrArg CosimplicialTotalization.map
    (UnderlyingWeightedCochains.pointedUnderlyingIso_natural C τ)
  rw [CosimplicialTotalization.map_comp, CosimplicialTotalization.map_comp] at hφ
  change CosimplicialTotalization.map c ≫ CosimplicialTotalization.map φE.hom =
    CosimplicialTotalization.map φD.hom ≫
      CosimplicialTotalization.map (UnderlyingWeightedCochains.map C t) at hφ
  have hδ := totalizationEndIso_natural W t
  have hε := PointedWeightedEnd.underlyingIso_natural W τ
  change (PointedWeightedEnd.map W τ).right ≫ εE.hom =
    εD.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W t at hε
  apply Under.UnderMorphism.ext
  apply (cancel_mono εE.hom).mp
  change (CosimplicialTotalization.map c ≫
      ((CosimplicialTotalization.map φE.hom ≫ δE.hom) ≫ εE.inv)) ≫ εE.hom =
    (((CosimplicialTotalization.map φD.hom ≫ δD.hom) ≫ εD.inv) ≫
      (PointedWeightedEnd.map W τ).right) ≫ εE.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hε]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hφ, Category.assoc, hδ]

end

end SerrePositivity.KST.Spectra.SimplexDensity
