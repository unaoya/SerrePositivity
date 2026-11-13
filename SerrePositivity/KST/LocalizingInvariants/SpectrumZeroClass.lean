module

public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows
public import SerrePositivity.KST.Spectra.SpectrumZeroMaps
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.ZeroHomotopy

/-!
概要：元の BF 零射と fiber 包含の零合成を h Sp の零射に同定する。
方針：一点スペクトルによる因子分解と、元の fiber 四角形の二辺の比較を使う。
規約：Sp の安定性は使わない。使われ方：分裂比較の射影補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance zeroClassSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance zeroClassHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

local instance zeroClassHoZero :
    HasZeroMorphisms (hoFunctor.obj (SimplicialNerve OmegaSpectrum.{u})) :=
  inferInstanceAs (HasZeroMorphisms (hoFunctor.obj Sp.{u}))

lemma hom_zero (X Y : OmegaSpectrum.{u}) : hom (0 : X ⟶ Y) = 0 := by
  have h : (0 : X ⟶ Y) = point_isZero.from_ X ≫ point_isZero.to_ Y := rfl
  rw [h, hom_comp]
  have hz : IsZero (obj _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u}) := pointZeroVertex.isZero.isZeroHo
  rw [hz.eq_zero_of_src (hom (point_isZero.to_ Y)), comp_zero]

lemma fiber_inclusion_comp {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    hom (homotopyFiberInclusion f) ≫ hom f = 0 := by
  apply (cancel_epi (FiberModel.fiberObjectIso f).hom).mp
  rw [← Category.assoc, FiberModel.bottom_naturality, Category.assoc,
    FiberModel.right_naturality, ← Category.assoc,
    (FiberModel.homotopyFiberSquare f).toZeroTriangle.homMk_comp_eq_zero]
  simp

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
