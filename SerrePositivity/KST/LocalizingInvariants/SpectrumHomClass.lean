module

public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
概要：元の BF 射を Sp のホモトピー圏の射として扱う界面。
方針：元の coherent 辺の類を取り、既存の恒等・合成三角形を使う。
規約：新しいホモトピー圏を定義しない。使われ方：K-5 の包含と長完全列の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance spectrumClassSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

abbrev obj (X : OmegaSpectrum.{u}) : hoFunctor.obj Sp.{u} :=
  SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)

/-- 元の BF 射の、Sp の実際のホモトピー圏における類。 -/
def hom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated

lemma hom_id (X : OmegaSpectrum.{u}) : hom (𝟙 X) = 𝟙 (obj X) := by
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 X)).toTruncated = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id]
  exact SSet.Truncated.HomotopyCategory.homMk_id _

lemma hom_comp {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom (f ≫ g) = hom f ≫ hom g :=
  (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).toTruncated).symm

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
