module

public import SerrePositivity.KST.LocalizingInvariants.FiberLongExact
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi

/-!
概要：任意の Sp の実 fiber 四角形の整数 π 長完全列。
方針：元の右辺を BF 射として復号し、元の四角形を変更せず比較定理へ渡す。
規約：右辺を BF 射に限定する仮定はない。使われ方：局所化不変量の像の長完全列。
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
namespace SerrePositivity.KST.LocalizingInvariants.NativeFiber

local instance nativeFiberSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})

def rightMap := SpectrumHo.edgeMap (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow t.square))

/-- 同じ実四角形を、復号した右辺の fiber 四角形として表示する。 -/
def asFiberSquare (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (rightMap t)).toTruncated where
  square := t.square
  zero_corner := t.zero_corner
  right_edge := by
    apply SSet.yonedaEquiv.injective
    exact ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge t.square).symm.trans
      (SpectrumHo.edgeMap_edge (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow t.square))).symm).trans
        (SSet.yonedaEquiv.apply_symm_apply _).symm
  isPullback := ht

/-- 元の四角形の各頂点での整数 π 群。 -/
abbrev group (i k : Fin 2) (j : ℤ) :=
  (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex t.square i k)

def bottom (j : ℤ) : group t 0 0 j →* group t 1 0 j :=
  ((SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom t.square)).hom

def right (j : ℤ) : group t 1 0 j →* group t 1 1 j :=
  ((SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight t.square)).hom

def boundary (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) : group t 1 1 (j + 1) →* group t 0 0 j :=
  FiberPi.boundary (rightMap t) (asFiberSquare t ht) j

lemma exact_fiber (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) (a : group t 0 0 j) :
    bottom t j a = 1 ↔ ∃ b : group t 1 1 (j + 1), boundary t ht j b = a :=
  FiberPi.exact_fiber (rightMap t) (asFiberSquare t ht) j a

lemma exact_total (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) (a : group t 1 0 j) :
    right t j a = 1 ↔ ∃ b : group t 0 0 j, bottom t j b = a :=
  FiberPi.exact_total (rightMap t) (asFiberSquare t ht) j a

lemma exact_base (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) (a : group t 1 1 (j + 1)) :
    boundary t ht j a = 1 ↔ ∃ b : group t 1 0 (j + 1), right t (j + 1) b = a :=
  FiberPi.exact_base (rightMap t) (asFiberSquare t ht) j a

end SerrePositivity.KST.LocalizingInvariants.NativeFiber
