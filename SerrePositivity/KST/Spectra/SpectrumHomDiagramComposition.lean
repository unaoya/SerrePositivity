module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitHomHolim
public import SerrePositivity.KST.Spectra.RawSpectrumUnpointedWeightedComposition
public import SerrePositivity.KST.Spectra.WeightedParameterNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConePrecomposition

/-!
概要：raw Hom の係数図式の同型は、元の豊穣 Hom の前合成作用を保つ。
方針：各成分の元の合成を同定し、共有のパラメータ作用の係数自然性を適用する。
規約：同型の順射を変更しない。使われ方：BF Hom 比較の元の図式上での豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance diagramParamSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I]

/-- 元の Hom 図式への同型の各成分は、元の豊穣合成と可換。 -/
lemma rawSimplicialHomDiagramIso_parameter (X Y : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    (rawSimplicialHomDiagramIso Y D).hom.app i ▷ mappingSpace X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram D X Y).app i =
      (Functor.whiskerLeft (D ⋙ forgetToKan)
        (RawSpectrumMapping.compositionParameterTransformation X Y)).app i ≫
          (rawSimplicialHomDiagramIso X D).hom.app i := by
  change (𝟙 (mappingSpace Y (D.obj i))) ▷ mappingSpace X Y ≫
    ((β_ (mappingSpace Y (D.obj i)) (mappingSpace X Y)).hom ≫
      mappingComposition X Y (D.obj i)) =
    ((β_ (RawSpectrumMapping.space Y (D.obj i).toKanSequence)
      (RawSpectrumMapping.space X Y.toKanSequence)).hom ≫
      RawSpectrumMapping.composition X Y (D.obj i).toKanSequence) ≫ 𝟙 _
  rw [id_whiskerRight, Category.id_comp, Category.comp_id,
    RawSpectrumMapping.composition_spectrum]
  rfl

/-- 元の Hom 図式への同型は、共有の end のパラメータ作用と可換。 -/
lemma unpointedWeightedComposition_diagramIso (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    RawSpectrumMapping.unpointedWeightedComposition X Y W (D ⋙ forgetToKan) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (rawSimplicialHomDiagramIso X D).hom =
      (𝟙 (mappingSpace X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (rawSimplicialHomDiagramIso Y D).hom) ≫
        (β_ (mappingSpace X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D Y))).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram D X Y) := by
  have h := WeightedParameterNaturality.natural W
    (rawSimplicialHomDiagramIso Y D).hom (rawSimplicialHomDiagramIso X D).hom
    (Functor.whiskerLeft (D ⋙ forgetToKan)
      (RawSpectrumMapping.compositionParameterTransformation X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram D X Y)
    (rawSimplicialHomDiagramIso_parameter X Y D)
  dsimp only [RawSpectrumMapping.unpointedWeightedComposition]
  rw [Category.assoc, ← h, ← BraidedCategory.braiding_naturality_right_assoc,
    id_tensorHom]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
