module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitEndPoint

/-!
概要：構成済みの Hom end の三つの点を単位からの射として取り、左右の射影と照合する。
方針：零単体と単位からの射の全単射を用い、元の恒等射の豊穣表示を同定する。
規約：切断点を取り替えない。使われ方：全 Hom パラメータの比較族の固定点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
/-- 零単体による単位からの射は、単体集合の後合成に自然。 -/
lemma unitPoint_comp {A B : SSet.{u}} (p : A _⦋0⦌) (f : A ⟶ B) :
    A.unitHomEquiv.symm p ≫ f = B.unitHomEquiv.symm (f.app _ p) := by
  apply B.unitHomEquiv.injective
  change f.app _ (A.unitHomEquiv (A.unitHomEquiv.symm p)) =
    B.unitHomEquiv (B.unitHomEquiv.symm (f.app _ p))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
namespace OmegaSpectrum
local instance pointUnitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance pointUnitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance pointUnitRawCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance pointUnitCoefficientKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance pointUnitEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)
/-- 元の Hom end の恒等射の像を、単位からの射として取る。 -/
def homotopyLimitHomEndPointMap (D : I ⥤ OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))).unitHomEquiv.symm
    (homotopyLimitHomEndPoint D)

/-- 元の共通解像の切断点を単位からの射として取る。 -/
def homotopyLimitEdgewiseEndPointMap (D : I ⥤ OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor)).unitHomEquiv.symm
      (homotopyLimitEdgewiseEndPoint D)

/-- 元の反転 end の切断点を単位からの射として取る。 -/
def homotopyLimitReflectedEndPointMap (D : I ⥤ OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)).unitHomEquiv.symm
      (homotopyLimitReflectedEndPoint D)

/-- 元の end の点の射は、元の恒等射の豊穣表示を比較で送った射そのもの。 -/
lemma homotopyLimitHomEndPointMap_eq (D : I ⥤ OmegaSpectrum.{u}) :
    homotopyLimitHomEndPointMap D =
      mappingIdentity (homotopyLimit D) ≫
        (homotopyLimitHomHolimEquivalence (homotopyLimit D) D).hom := by
  dsimp only [homotopyLimitHomEndPointMap]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))).unitHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  dsimp only [homotopyLimitHomEndPoint, SimplicialCategory.homEquiv', Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl
/-- 共通解像の点の射の右射影は元の end の点の射。 -/
lemma homotopyLimitEdgewiseEndPointMap_right (D : I ⥤ OmegaSpectrum.{u}) :
    homotopyLimitEdgewiseEndPointMap D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))) =
        homotopyLimitHomEndPointMap D := by
  dsimp only [homotopyLimitEdgewiseEndPointMap, homotopyLimitHomEndPointMap]
  rw [unitPoint_comp]
  erw [homotopyLimitEdgewiseEndPoint_projection]
  rfl

/-- 共通解像の点の射の左射影は元の反転 end の点の射。 -/
lemma homotopyLimitEdgewiseEndPointMap_left (D : I ⥤ OmegaSpectrum.{u}) :
    homotopyLimitEdgewiseEndPointMap D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))) =
        homotopyLimitReflectedEndPointMap D := by
  dsimp only [homotopyLimitEdgewiseEndPointMap, homotopyLimitReflectedEndPointMap]
  rw [unitPoint_comp]
  rfl

end OmegaSpectrum
end SerrePositivity.KST.Spectra
