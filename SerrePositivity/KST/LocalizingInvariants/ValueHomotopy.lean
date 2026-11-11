module

public import SerrePositivity.KST.LocalizingInvariants.Invariant
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：Sp 値 ∞ 関手の値と全整数次数の同値検出。
方針：値の頂点と辺を BF 対象・実射へ戻し、Sp-5 d1 の判定を同じ辺へ適用する。
規約：Sp の安定性は使わない。使われ方：局所化不変量の長完全列の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance valueSimplicialCategory : SimplicialCategory Spectra.OmegaSpectrum.{u} :=
  Spectra.OmegaSpectrum.simplicialCategory

/-- Sp 値 ∞ 関手の指定された安定圏での実 BF 対象。 -/
def value (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    Spectra.OmegaSpectrum.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := Spectra.OmegaSpectrum.{u})
    (E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A))

/-- 値の BF 対象を戻すと、元の Sp の同じ頂点である。 -/
lemma value_vertex (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value E A) = E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _

/-- 完全関手の像を端点付きの BF 射として読む。 -/
def valueMap (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u})
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) : value E A ⟶ value E B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (C := Spectra.OmegaSpectrum.{u})
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).map E).ofEq (value_vertex E A).symm (value_vertex E B).symm)

/-- 戻した BF 射の辺は、元の関手が写した Sp の同じ一単体。 -/
lemma valueMap_edge (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u})
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E F)).edge =
      E.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge :=
  congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).map E).ofEq (value_vertex E A).symm (value_vertex E B).symm))

/-- 指定された安定圏での全整数次数の群。 -/
abbrev valueHomotopyGroup (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u})
    (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (j : ℤ) := Spectra.OmegaSpectrum.homotopyGroup (value E A) j

/-- 誘導された群準同型は元の Sp の辺から復元した BF 射のもの。 -/
def valueHomotopyMap (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u})
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (j : ℤ) :
    valueHomotopyGroup E A j →* valueHomotopyGroup E B j :=
  Spectra.OmegaSpectrum.homotopyMap (valueMap E F) j

/-- 全整数 π の同型性は局所化不変量の元の像の辺の同値性を検出する。 -/
theorem value_isInvertible_of_piIsomorphism (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u})
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hF : ∀ j : ℤ, Function.Bijective (valueHomotopyMap E F j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).map E).toTruncated := by
  have h := Spectra.OmegaSpectrum.isInvertible_of_piIsomorphism (valueMap E F) hF
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (valueMap_edge E F)).mp h

end SerrePositivity.KST.LocalizingInvariants
