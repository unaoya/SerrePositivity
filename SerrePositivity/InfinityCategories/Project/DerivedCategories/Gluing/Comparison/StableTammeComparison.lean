module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.StableLaxStructure
public import SerrePositivity.KST.LocalizingInvariants.TammeProjectionEquivalence
/-!
概要：元 gluing の局所化不変量の分裂を、K-8b の元の両射影を持つ積同値へ接続する。
方針：正本比較の両往復関手同型を同じ値関手で写し、公開済みの Tamme 同値と合成する。
規約：二脚の完全性は上流供給待ちの明示入力。一般の安定圏上の K は定義しない。
使われ方：D-14 の供給後の G-1 e の分裂整合と K-8 d8 の射影照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants KST.Spectra
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
def dgGluingStableComparisonInverse : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M⟩
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v w} ⟶ Sp.{max (u + 1) v w})
def dgGluingStableComparisonValueIso :
    SpectrumHo.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)) ≅
      SpectrumHo.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)) where
  hom := SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD))
  inv := SpectrumHo.hom (valueMap Φ (dgGluingStableComparisonInverse R C D M hC hD))
  hom_inv_id := by
    let f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD
    let g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
      dgGluingStableComparisonInverse R C D M hC hD
    let fg : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) := ⟨f.hom ≫ g.hom, inferInstance⟩
    have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso fg.hom (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD).obj) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).homInvIso
    have h := valueMap_hom_eq_of_functorIso Φ (F := fg)
      (G := 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)) e
    change (stableValueFunctor Φ).map f ≫ (stableValueFunctor Φ).map g = _
    rw [← Functor.map_comp]
    exact h.trans ((stableValueFunctor Φ).map_id _)
  inv_hom_id := by
    let f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD
    let g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD) :=
      dgGluingStableComparisonInverse R C D M hC hD
    let gf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD) := ⟨g.hom ≫ f.hom, inferInstance⟩
    have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso gf.hom (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD).obj) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).invHomIso
    have h := valueMap_hom_eq_of_functorIso Φ (F := gf)
      (G := 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD)) e
    change (stableValueFunctor Φ).map g ≫ (stableValueFunctor Φ).map f = _
    rw [← Functor.map_comp]
    exact h.trans ((stableValueFunctor Φ).map_id _)
variable (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
  (hΦ : IsLocalizingInvariant Φ)
def dgGluingTammeProjectionEquivalence :
    SpectrumHo.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableObject R C D M hC hD)) ≅
      SpectrumHo.obj (Binary.obj (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC))
        (value Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD))) :=
  dgGluingStableComparisonValueIso R C D M hC hD Φ ≪≫
    hΦ.tammeProjectionEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC hY)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD hM)
lemma dgGluingTammeProjectionEquivalence_fst :
    (dgGluingTammeProjectionEquivalence R C D M hC hD Φ hY hM hΦ).hom ≫
      SpectrumHo.hom (Binary.fst _ _) =
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLeftProjection R C D M hC hD)) := by
  rw [dgGluingTammeProjectionEquivalence, Iso.trans_hom, Category.assoc]
  change SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD)) ≫
    (hΦ.tammeProjectionEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC hY)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD hM)).hom ≫ _ = _
  rw [hΦ.tammeProjectionEquivalence_fst]
  change (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD) ≫
    (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxFst R C D M hC hD) = _
  rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison_fst]
  rfl
lemma dgGluingTammeProjectionEquivalence_snd :
    (dgGluingTammeProjectionEquivalence R C D M hC hD Φ hY hM hΦ).hom ≫
      SpectrumHo.hom (Binary.snd _ _) =
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableRightProjection R C D M hC hD)) := by
  rw [dgGluingTammeProjectionEquivalence, Iso.trans_hom, Category.assoc]
  change SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD)) ≫
    (hΦ.tammeProjectionEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC hY)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD hM)).hom ≫ _ = _
  rw [hΦ.tammeProjectionEquivalence_snd]
  change (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison R C D M hC hD) ≫
    (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxSnd R C D M hC hD) = _
  rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableComparison_snd]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
