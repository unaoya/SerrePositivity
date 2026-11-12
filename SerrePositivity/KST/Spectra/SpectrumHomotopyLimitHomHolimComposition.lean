module

public import SerrePositivity.KST.Spectra.SpectrumHomDiagramComposition
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitUnderlyingComposition

/-!
概要：元の BF Hom–Bousfield–Kan end 同値の順射は、共有の豊穣前合成作用と可換。
方針：元の比較の順射を忘却比較と係数同型に分解し、証明済みの二つの自然性を合成する。
規約：元の simplicialHomDiagram と比較射を保持する。使われ方：普遍切断の前合成公式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance homHolimCompositionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homHolimCompositionHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance homHolimCompositionCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance homHolimCompositionDiagramKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance homHolimCompositionEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)

/-- 元の BF Hom 同値の順射は、忘却比較と元の係数同型の合成。 -/
lemma homotopyLimitHomHolimEquivalence_hom_factor (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    (homotopyLimitHomHolimEquivalence X D).hom =
      homotopyLimitUnderlyingMappingComparison X D ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (rawSimplicialHomDiagramIso X D).hom := by
  change (RawSpectrumMapping.post X (homotopyLimitProjection D) ≫
      (RawSpectrumMapping.homotopyLimitIso X (D ⋙ forgetToKan)).hom.right) ≫
      ((PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (rawSimplicialHomDiagramIso X D).hom) = _
  dsimp only [homotopyLimitUnderlyingMappingComparison, homotopyLimitPointedMappingComparison]
  simp only [Under.comp_right, Category.assoc]
  rfl

/-- 元の BF Hom 同値の順射は、元の Hom 図式の全パラメータの前合成に厳密に自然。 -/
lemma homotopyLimitHomHolimEquivalence_composition (X Y : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    mappingComposition X Y (homotopyLimit D) ≫ (homotopyLimitHomHolimEquivalence X D).hom =
      (𝟙 (mappingSpace X Y) ⊗ₘ (homotopyLimitHomHolimEquivalence Y D).hom) ≫
        (β_ (mappingSpace X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D Y))).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram D X Y) := by
  rw [homotopyLimitHomHolimEquivalence_hom_factor,
    homotopyLimitHomHolimEquivalence_hom_factor,
    ← Category.assoc, homotopyLimitUnderlyingMappingComparison_composition,
    Category.assoc, unpointedWeightedComposition_diagramIso,
    ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
