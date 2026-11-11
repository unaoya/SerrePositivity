module

public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.FiberDetection

/-!
概要：任意の Sp fiber 列の全整数 π 消滅から元の第二辺の同値性を検出する。
方針：同じ元の右辺の BF fiber への群同型で消滅を移し、d1 の判定を使う。
規約：fiber 頂点の同定を追加仮定にしない。使われ方：局所化不変量の基本補題。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.NativeFiber

local instance nativeDetectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 全整数 π の消滅は、任意の実 fiber 列の元の第二辺の同値性を検出する。 -/
lemma isInvertible_of_fiberGroups (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u}) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t)
    (hF : ∀ j : ℤ, Subsingleton (group t 0 0 j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow t.square) := by
  have h : ∀ j : ℤ, Subsingleton (homotopyGroup (homotopyFiber (rightMap t)) j) := by
    intro j
    let e := FiberPi.fiberEquiv (rightMap t) (asFiberSquare t ht) j
    have hn : Subsingleton (FiberPi.fiberGroup (rightMap t) (asFiberSquare t ht) j) := hF j
    exact ⟨fun a b ↦ e.symm.injective (hn.elim _ _)⟩
  have hf := FiberDetection.isInvertible_of_fiberGroups (rightMap t) h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (SpectrumHo.edgeMap_edge (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow t.square)))).mp hf

end SerrePositivity.KST.LocalizingInvariants.NativeFiber
