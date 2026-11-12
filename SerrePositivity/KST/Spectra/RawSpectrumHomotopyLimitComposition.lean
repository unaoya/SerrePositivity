module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorComposition
public import SerrePositivity.KST.Spectra.RawSpectrumWeightedComposition
public import SerrePositivity.KST.Spectra.RawSpectrumHomotopyLimitIso

/-!
概要：元の Hom–end 交換の、源の全 Hom パラメータに関する豊穣自然性。
方針：元の射影による後合成、cotensor 交換の豊穣自然性、係数から作った end の作用を使う。
規約：点つき smash 上の実際の射の等式。使われ方：coherent な極限錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance homotopyEndCompositionSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 元の Hom–end 交換の各射影は、全 Hom パラメータの合成と可換。 -/
lemma homotopyLimitIso_composition_component {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u})
    (D : I ⥤ KanSequence.{u}) (i : I) :
    pointedComposition X Y (KanSequence.homotopyLimit D) ≫ (homotopyLimitIso X D).hom ≫
        end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ pointedFunctor X)) i =
      (𝟙 (pointedSpace X Y.toKanSequence) ⊗ₘ
        ((homotopyLimitIso Y D).hom ≫
          end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ pointedFunctor Y)) i)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map (pointedSpace X Y.toKanSequence)
          (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (pointedSpace Y (D.obj i)) ≫
          (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).map
            (pointedComposition X Y (D.obj i)) := by
  rw [homotopyLimitIso_hom_π, homotopyLimitIso_hom_π,
    ← Category.assoc, pointedComposition_post, Category.assoc]
  dsimp only [cotensorIso]
  rw [cotensorComparison_composition, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp]

/-- 元の Hom–end 交換は、係数から構成した end の全 Hom 作用に厳密に自然。 -/
lemma homotopyLimitIso_composition {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u}) (D : I ⥤ KanSequence.{u}) :
    pointedComposition X Y (KanSequence.homotopyLimit D) ≫ (homotopyLimitIso X D).hom =
      (𝟙 (pointedSpace X Y.toKanSequence) ⊗ₘ (homotopyLimitIso Y D).hom) ≫
        weightedComposition X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D := by
  apply end_.hom_ext
  intro i
  conv_lhs => rw [Category.assoc]
  conv_rhs =>
    rw [Category.assoc, weightedComposition_π, ← Category.assoc,
      tensorHom_comp_tensorHom, Category.id_comp]
  exact homotopyLimitIso_composition_component X Y D i

end SerrePositivity.KST.Spectra.RawSpectrumMapping
