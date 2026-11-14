module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitPointMaps
public import SerrePositivity.KST.Spectra.EdgewiseHomEndPrecomposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ParameterPoint

/-!
概要：元の BF 恒等射の像の全 Hom 前合成族は、元の BF Hom–end 同値に一致。
方針：比較の豊穣自然性を恒等射へ制限し、豊穣合成の右単位律を適用する。
規約：別の同値を選ばず、元の比較の順射を回収する。使われ方：共通解像の比較族の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance homEndFamilySimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homEndFamilyHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance homEndFamilyRawCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance homEndFamilyCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance homEndFamilyEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)
/-- 元の恒等射の像で end の前合成作用を固定した、全 Hom パラメータの族。 -/
def homotopyLimitHomEndFamily (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    mappingSpace X (homotopyLimit D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (homotopyLimitHomEndPointMap D) (mappingSpace X (homotopyLimit D)) ≫
    homEndPrecomposition D X (homotopyLimit D)

/-- 恒等射の像の前合成族は、既存の BF Hom–end 同値の順射そのもの。 -/
lemma homotopyLimitHomEndFamily_eq (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    homotopyLimitHomEndFamily D X = (homotopyLimitHomHolimEquivalence X D).hom := by
  let L := homotopyLimit D
  let A := mappingSpace X L
  have h := congrArg (fun f ↦ (ρ_ A).inv ≫ A ◁ mappingIdentity L ≫ f)
    (homotopyLimitHomHolimEquivalence_composition X L D)
  simp only [id_tensorHom] at h
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc,
    rightUnitor_inv_braiding_assoc] at h
  have hl := congrArg (fun f ↦ f ≫ (homotopyLimitHomHolimEquivalence X D).hom)
    (mappingComposition_identity X L)
  simp only [Category.id_comp, Category.assoc] at hl
  dsimp only [homotopyLimitHomEndFamily, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family]
  rw [homotopyLimitHomEndPointMap_eq]
  exact (Category.assoc _ _ _).trans (h.symm.trans hl)

end SerrePositivity.KST.Spectra.OmegaSpectrum
