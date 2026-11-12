module

public import SerrePositivity.KST.LocalizingInvariants.AbstractFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.ValueHomotopy
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-!
概要：抽象 Verdier 列の像の三対象と二辺を、元の値と誘導準同型に照合する。
方針：四角形提示の頂点等号を π 関手で写し、元の BF 射との自然性を使う。
規約：包含・商の元の一単体を保持する。使われ方：局所化不変量の値の長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

local instance invariantPiSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hE : IsLocalizingInvariant E)
  (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})

lemma fiber_left_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (hE.abstractFiberTriangle d).square 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value E d.left) := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square 0 0) = _
  exact (congrArg (E.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).left_eq).trans
    (value_vertex E d.left).symm

lemma fiber_middle_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (hE.abstractFiberTriangle d).square 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value E d.middle) := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square 1 0) = _
  exact (congrArg (E.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).middle_eq).trans
    (value_vertex E d.middle).symm

lemma fiber_right_vertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (hE.abstractFiberTriangle d).square 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value E d.right) := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square 1 1) = _
  exact (congrArg (E.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).right_eq).trans
    (value_vertex E d.right).symm

def fiberLeftIso : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 0 0 ≅
    SpectrumHo.obj (value E d.left) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (hE.fiber_left_vertex d))

def fiberMiddleIso : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 1 0 ≅
    SpectrumHo.obj (value E d.middle) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (hE.fiber_middle_vertex d))

def fiberRightIso : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 1 1 ≅
    SpectrumHo.obj (value E d.right) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (hE.fiber_right_vertex d))

lemma fiber_bottom_naturality : (hE.fiberLeftIso d).hom ≫
      SpectrumHo.hom (valueMap E d.inclusion) =
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (hE.abstractFiberTriangle d).square ≫ (hE.fiberMiddleIso d).hom := by
  have he : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (hE.abstractFiberTriangle d).square).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E d.inclusion)).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, hE.abstractFiberTriangle_bottom, Equiv.apply_symm_apply]
    exact (valueMap_edge E d.inclusion).symm
  exact (FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (hE.abstractFiberTriangle d).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E d.inclusion)).toTruncated
    (hE.fiber_left_vertex d) (hE.fiber_middle_vertex d) he).symm

lemma fiber_right_naturality : (hE.fiberMiddleIso d).hom ≫
      SpectrumHo.hom (valueMap E d.projection) =
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (hE.abstractFiberTriangle d).square ≫ (hE.fiberRightIso d).hom := by
  have he : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (hE.abstractFiberTriangle d).square).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E d.projection)).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge, hE.abstractFiberTriangle_right, Equiv.apply_symm_apply]
    exact (valueMap_edge E d.projection).symm
  exact (FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (hE.abstractFiberTriangle d).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E d.projection)).toTruncated
    (hE.fiber_middle_vertex d) (hE.fiber_right_vertex d) he).symm

def fiberLeftGroupIso (j : ℤ) :
    NativeFiber.group (hE.abstractFiberTriangle d) 0 0 j ≅
      CommGrpCat.of (valueHomotopyGroup E d.left j) :=
  (SpectrumHo.piFunctor j).mapIso (hE.fiberLeftIso d) ≪≫ SpectrumHo.piComparison _ j

def fiberMiddleGroupIso (j : ℤ) :
    NativeFiber.group (hE.abstractFiberTriangle d) 1 0 j ≅
      CommGrpCat.of (valueHomotopyGroup E d.middle j) :=
  (SpectrumHo.piFunctor j).mapIso (hE.fiberMiddleIso d) ≪≫ SpectrumHo.piComparison _ j

def fiberRightGroupIso (j : ℤ) :
    NativeFiber.group (hE.abstractFiberTriangle d) 1 1 j ≅
      CommGrpCat.of (valueHomotopyGroup E d.right j) :=
  (SpectrumHo.piFunctor j).mapIso (hE.fiberRightIso d) ≪≫ SpectrumHo.piComparison _ j

lemma fiber_bottom_group_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (hE.abstractFiberTriangle d).square) ≫
        (hE.fiberMiddleGroupIso d j).hom =
      (hE.fiberLeftGroupIso d j).hom ≫ CommGrpCat.ofHom (valueHomotopyMap E d.inclusion j) :=
  FiberPi.group_naturality _ _ (hE.fiberLeftIso d) (hE.fiberMiddleIso d)
    (hE.fiber_bottom_naturality d) j

lemma fiber_right_group_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (hE.abstractFiberTriangle d).square) ≫
        (hE.fiberRightGroupIso d j).hom =
      (hE.fiberMiddleGroupIso d j).hom ≫ CommGrpCat.ofHom (valueHomotopyMap E d.projection j) :=
  FiberPi.group_naturality _ _ (hE.fiberMiddleIso d) (hE.fiberRightIso d)
    (hE.fiber_right_naturality d) j

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
