module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitEdgewiseFamilies

/-!
概要：元の反転 end の切断点から得た全 Hom 比較族は、実際の単体的ホモトピー同値。
方針：右射影の先の比較を元の BF Hom 同値と同定し、左右の射影の同値性を順に消去する。
規約：選んだ切断の自然性を仮定しない。使われ方：coherent 錐の native な極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance reflectedFamilyEquivalenceSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance reflectedFamilyEquivalenceHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance reflectedFamilyEquivalenceRawCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance reflectedFamilyEquivalenceCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance reflectedFamilyEquivalenceEndKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram D X)) :=
  bousfieldKanHolim_kanComplex (simplicialHomDiagram D X)

local instance reflectedFamilyEquivalenceEdgewiseCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((simplicialHomDiagram D X ⋙ edgewiseSubdivisionFunctor).obj i) :=
  inferInstanceAs (KanComplex (edgewiseSubdivision (mappingSpace X (D.obj i))))
local instance reflectedFamilyEquivalenceOppositeCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((simplicialHomDiagram D X ⋙ SSet.opFunctor).obj i) :=
  inferInstanceAs (KanComplex (mappingSpace X (D.obj i)).op)
local instance reflectedFamilyEquivalenceEdgewiseEndKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram D X ⋙ edgewiseSubdivisionFunctor)) :=
  bousfieldKanHolim_kanComplex _
local instance reflectedFamilyEquivalenceOppositeEndKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram D X ⋙ SSet.opFunctor)) :=
  bousfieldKanHolim_kanComplex _

/-- 共通解像の点の全 Hom 比較族は、右射影の可換四角形からホモトピー同値。 -/
lemma homotopyLimitEdgewiseEndFamily_homotopyEquivalence
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsSimplicialHomotopyEquivalence (homotopyLimitEdgewiseEndFamily D X) := by
  have hq : IsSimplicialHomotopyEquivalence (homotopyLimitHomEndFamily D X) := by
    rw [homotopyLimitHomEndFamily_eq]
    exact homotopyLimitHomHolim_homotopyEquivalence X D
  have rightSourceTrivial : TrivialKanFibration
      (edgewiseRight (mappingSpace X (homotopyLimit D))) :=
    edgewiseRight_trivialKanFibration _
  have hs := (isQCatEquivalence_of_trivialKanFibration
    (edgewiseRight (mappingSpace X (homotopyLimit D)))).isSimplicialHomotopyEquivalence
  have h := hs.comp hq
  rw [← homotopyLimitEdgewiseEndFamily_right] at h
  exact (bousfieldKanEdgewiseRight_homotopyEquivalence (simplicialHomDiagram D X)).cancel_right h

/-- 元の反転 end の点の全 Hom 比較族は、左射影の可換四角形からホモトピー同値。 -/
lemma homotopyLimitReflectedEndFamily_homotopyEquivalence
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsSimplicialHomotopyEquivalence (homotopyLimitReflectedEndFamily D X) := by
  have leftSourceTrivial : TrivialKanFibration
      (edgewiseLeft (mappingSpace X (homotopyLimit D))) :=
    edgewiseLeft_trivialKanFibration _
  have hs := (isQCatEquivalence_of_trivialKanFibration
    (edgewiseLeft (mappingSpace X (homotopyLimit D)))).isSimplicialHomotopyEquivalence
  have h := (homotopyLimitEdgewiseEndFamily_homotopyEquivalence D X).comp
    (bousfieldKanEdgewiseLeft_homotopyEquivalence (simplicialHomDiagram D X))
  rw [homotopyLimitEdgewiseEndFamily_left] at h
  exact hs.cancel_left h

end SerrePositivity.KST.Spectra.OmegaSpectrum
