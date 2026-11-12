module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxInvariantDiagonal

/-!
概要：普遍差への比較の値と実積射の可換性を、元の両射影で証明する。
方針：J の第一射影の全関手同型・第二射影の厳密等式を値に写す。
規約：整数 π の一致から射の一致を推論しない。使われ方：実積正方形の右辺の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def legMap : Binary.obj (value Φ C) (value Φ D) ⟶ Binary.obj (value Φ Q) (value Φ Q) :=
  Binary.lift (Binary.fst _ _ ≫ valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r))
    (Binary.snd _ _ ≫ valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r))

lemma legMap_fst : legMap (Φ := Φ) p q r ≫ Binary.fst _ _ =
    Binary.fst _ _ ≫ valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r) := Binary.lift_fst _ _

lemma legMap_snd : legMap (Φ := Φ) p q r ≫ Binary.snd _ _ =
    Binary.snd _ _ ≫ valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r) := Binary.lift_snd _ _

lemma lift_value_fst : SpectrumHo.hom (valueMap Φ (LaxUniversalDifference.exactLift p q r)) ≫
    SpectrumHo.hom (valueMap Φ (laxFst (𝟙 Q) (𝟙 Q))) =
      SpectrumHo.hom (valueMap Φ (laxFst p q)) ≫
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)) := by
  let f : laxCategory p q ⟶ Q := LaxUniversalDifference.exactLift p q r ≫ laxFst (𝟙 Q) (𝟙 Q)
  let g : laxCategory p q ⟶ Q := laxFst p q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso p q r
  have he := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at he
  change (stableValueFunctor Φ).map (LaxUniversalDifference.exactLift p q r) ≫
    (stableValueFunctor Φ).map (laxFst (𝟙 Q) (𝟙 Q)) =
      (stableValueFunctor Φ).map (laxFst p q) ≫
        (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)
  simpa only [f, g, CategoryTheory.Functor.map_comp] using he

lemma lift_value_snd : SpectrumHo.hom (valueMap Φ (LaxUniversalDifference.exactLift p q r)) ≫
    SpectrumHo.hom (valueMap Φ (laxSnd (𝟙 Q) (𝟙 Q))) =
      SpectrumHo.hom (valueMap Φ (laxSnd p q)) ≫
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)) := by
  let f : laxCategory p q ⟶ Q := LaxUniversalDifference.exactLift p q r ≫ laxSnd (𝟙 Q) (𝟙 Q)
  let g : laxCategory p q ⟶ Q := laxSnd p q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r
  have hfg : f.hom = g.hom := by
    change LaxUniversalDifference.lift p q r ≫ (laxSnd (𝟙 Q) (𝟙 Q)).hom =
      (laxSnd p q).hom ≫ (LaxInclusion.fromD p q ≫ r.hom)
    rw [LaxUniversalDifference.lift_snd, Category.assoc]
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom :=
    eqToIso (congrArg (fun a => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) hfg)
  have he := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at he
  change (stableValueFunctor Φ).map (LaxUniversalDifference.exactLift p q r) ≫
    (stableValueFunctor Φ).map (laxSnd (𝟙 Q) (𝟙 Q)) =
      (stableValueFunctor Φ).map (laxSnd p q) ≫
        (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)
  simpa only [f, g, CategoryTheory.Functor.map_comp] using he

lemma legMap_ho_fst : SpectrumHo.hom (legMap (Φ := Φ) p q r) ≫
    SpectrumHo.hom (Binary.fst _ _) = SpectrumHo.hom (Binary.fst _ _) ≫
      SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)) := by
  rw [← SpectrumHo.hom_comp, legMap_fst, SpectrumHo.hom_comp]

lemma legMap_ho_snd : SpectrumHo.hom (legMap (Φ := Φ) p q r) ≫
    SpectrumHo.hom (Binary.snd _ _) = SpectrumHo.hom (Binary.snd _ _) ≫
      SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)) := by
  rw [← SpectrumHo.hom_comp, legMap_snd, SpectrumHo.hom_comp]

lemma value_projection_comm :
    SpectrumHo.hom (valueMap Φ (LaxUniversalDifference.exactLift p q r)) ≫
        (hΦ.tammeProjectionEquivalence (𝟙 Q) (𝟙 Q)).hom =
      (hΦ.tammeProjectionEquivalence p q).hom ≫ SpectrumHo.hom (legMap (Φ := Φ) p q r) := by
  apply Binary.ho_hom_ext
  · rw [Category.assoc, hΦ.tammeProjectionEquivalence_fst, lift_value_fst,
      Category.assoc, legMap_ho_fst,
      ← Category.assoc, hΦ.tammeProjectionEquivalence_fst]
  · rw [Category.assoc, hΦ.tammeProjectionEquivalence_snd, lift_value_snd,
      Category.assoc, legMap_ho_snd,
      ← Category.assoc, hΦ.tammeProjectionEquivalence_snd]

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
