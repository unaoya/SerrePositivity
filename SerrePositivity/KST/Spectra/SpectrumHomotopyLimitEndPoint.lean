module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitHomHolimComposition
public import SerrePositivity.KST.Spectra.BousfieldKanEdgewiseEndLift

/-!
概要：元の BF 恒等射の Hom–end 比較の像を edgewise 共通解像に持ち上げ、反転係数の点にする。
方針：全境界 RLP から得た右切断で点を持ち上げ、左射影で反転した end へ送る。
規約：右射影は元の恒等射の像と厳密に一致する。使われ方：実際の coherent な錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance endPointSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance endPointHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance endPointRawCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance endPointCoefficientKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance endPointEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)

/-- 元の BF 恒等射を元の Hom–end 比較で送った切断点。 -/
def homotopyLimitHomEndPoint (D : I ⥤ OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))) _⦋0⦌ :=
  (homotopyLimitHomHolimEquivalence (homotopyLimit D) D).hom.app _
    (SimplicialCategory.homEquiv' (homotopyLimit D) (homotopyLimit D) (𝟙 _))

/-- 恒等射の像を、右 end 射影の全境界充填で共通解像へ持ち上げた点。 -/
def homotopyLimitEdgewiseEndPoint (D : I ⥤ OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor)) _⦋0⦌ :=
  (edgewiseEndRightSection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D))).app _
    (homotopyLimitHomEndPoint D)

/-- 共通解像の右射影は、元の BF 恒等射の比較の像そのもの。 -/
lemma homotopyLimitEdgewiseEndPoint_projection (D : I ⥤ OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D)))).app _
        (homotopyLimitEdgewiseEndPoint D) = homotopyLimitHomEndPoint D := by
  change (edgewiseEndRightSection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D)))).app _
        (homotopyLimitHomEndPoint D) = _
  rw [edgewiseEndRightSection_projection]
  rfl

/-- 共通解像の左射影で得た、反転した元の Hom 係数の end の点。 -/
def homotopyLimitReflectedEndPoint (D : I ⥤ OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D)))).app _
      (homotopyLimitEdgewiseEndPoint D)

end SerrePositivity.KST.Spectra.OmegaSpectrum
