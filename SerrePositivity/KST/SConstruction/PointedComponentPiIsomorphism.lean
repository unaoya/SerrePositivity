module
public import SerrePositivity.KST.SConstruction.PointedMappingLocalizedImage
public import SerrePositivity.KST.SConstruction.PointedPiLocalized
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison

/-! # 元の点つき成分に関する全基点 π 同型の不変性
概要：Kan 対象間の同じ点つき成分の射は、全基点 π 同型性を共有する。
方針：実成分の局所化像の等号と、点つき Whitehead・局所化検出を合成する。
規約：既存の同じ元の射を比較する。使われ方：BF 構造射の随伴の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping SerrePositivity.SimplicialModel

/-- 同じ点つき成分に属する Kan 対象間の射へ、全基点 π 同型性を移す。 -/
lemma kanPiIsomorphism_of_pointed_component
    {X Y : PointedSimplicialSet.{u}} [KanComplex X.right] [KanComplex Y.right]
    (f g : X ⟶ Y) (h : componentOf f = componentOf g) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right := by
  have he := pointedMappingImage_eq_of_component AnodyneHomotopy.anodyneQ
    (Localization.inverts _ anodyneExtensions) h
  have hi := pointed_localized_isIso_of_piIsomorphism g hg
  exact kanPiIsomorphism_of_localized_isIso f.right
    ((congrArg IsIso he).mpr hi)

end SerrePositivity.KST.SConstruction
