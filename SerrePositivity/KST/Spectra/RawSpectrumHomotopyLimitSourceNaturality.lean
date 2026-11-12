module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorSourceNaturality
public import SerrePositivity.KST.Spectra.RawSpectrumHomotopyLimitIso

/-!
概要：元の Hom と homotopy end の厳密な交換同型は、BF 源の厳密射に自然。
方針：全ての end の射影で、前合成・後合成の可換性と cotensor 交換の自然性を使う。
規約：源の通常の射についての自然性。全 Hom パラメータへの拡張は別工程。
使われ方：γ3 の coherent な極限錐への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance sourceHomotopyEndSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 元の Hom-end の各射影の比較は、源の射の前合成と可換。 -/
lemma homotopyLimitSource_component {I : Type u} [SmallCategory I]
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (D : I ⥤ KanSequence.{u}) (i : I) :
    pointedPre f (KanSequence.homotopyLimit D) ≫
        pointedPost X (KanSequence.homotopyLimitEvaluation D i) ≫
          (cotensorIso X (D.obj i) (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).hom =
      pointedPost Y (KanSequence.homotopyLimitEvaluation D i) ≫
        (cotensorIso Y (D.obj i) (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).hom ≫
          (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).map
            (pointedPre f (D.obj i)) := by
  let A := PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)
  have h : pointedPre f (KanSequence.mapping A (D.obj i)) ≫ (cotensorIso X (D.obj i) A).hom =
      (cotensorIso Y (D.obj i) A).hom ≫ (ihom A).map (pointedPre f (D.obj i)) :=
    cotensorComparison_pre_source f (D.obj i) A
  rw [← Category.assoc, ← pointedPre_post, Category.assoc, h]

/-- 各射影との可換式から得られる、点つき weighted end の比較の自然性。 -/
lemma weightedEnd_comparison_natural {I : Type u} [SmallCategory I]
    (W : I ⥤ SSet.{u}) {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E)
    {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (g : A ⟶ PointedWeightedEnd.obj W E) (h : B ⟶ PointedWeightedEnd.obj W D)
    (hc : ∀ i, g ≫ end_.π (PointedWeightedEnd.diagram W E) i =
      (f ≫ h) ≫ end_.π (PointedWeightedEnd.diagram W D) i ≫
        (ihom (PointedObject.adjoin (W.obj i))).map (τ.app i)) :
    g = f ≫ h ≫ PointedWeightedEnd.map W τ := by
  apply end_.hom_ext
  intro i
  rw [hc]
  simpa only [Category.assoc] using
    (congrArg (fun k ↦ f ≫ h ≫ k) (PointedWeightedEnd.map_π W τ i)).symm

/-- 元の Hom-end 交換の順射は、源の BF 射の前合成に厳密に自然。 -/
lemma homotopyLimitIso_pre {I : Type u} [SmallCategory I]
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (D : I ⥤ KanSequence.{u}) :
    pointedPre f (KanSequence.homotopyLimit D) ≫ (homotopyLimitIso X D).hom =
      (homotopyLimitIso Y D).hom ≫
        PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (Functor.whiskerLeft D (pointedPreTransformation f)) := by
  have h := weightedEnd_comparison_natural (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (Functor.whiskerLeft D (pointedPreTransformation f))
    (𝟙 (pointedSpace Y (KanSequence.homotopyLimit D)))
    (pointedPre f (KanSequence.homotopyLimit D) ≫ (homotopyLimitIso X D).hom)
    (homotopyLimitIso Y D).hom
  simp only [Category.id_comp] at h
  apply h
  intro i
  let a := (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).map
    (pointedPre f (D.obj i))
  exact (Category.assoc _ _ _).trans
    ((congrArg (pointedPre f (KanSequence.homotopyLimit D) ≫ ·)
      (homotopyLimitIso_hom_π X D i)).trans
      ((homotopyLimitSource_component f D i).trans
        (((congrArg (· ≫ a) (homotopyLimitIso_hom_π Y D i)).trans
          (Category.assoc _ _ _)).symm)))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
