module

public import SerrePositivity.KST.LocalizingInvariants.VerdierPresentation
public import SerrePositivity.KST.LocalizingInvariants.Invariant

/-!
概要：任意の抽象 Verdier 列から Sp の実際の fiber 列を得る。
方針：構成した四角形提示に局所化不変量の保存条件を適用する。
規約：元の包含と商の像の辺を保持する。使われ方：K-5 の長完全列の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
namespace IsLocalizingInvariant
variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}} (hE : IsLocalizingInvariant E)
include hE

/-- 任意抽象 Verdier 列の像の零角付き四角形。 -/
def abstractFiberTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Spectra.Sp.{u} :=
  hE.fiberTriangle (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d)

/-- 提示の存在を仮定せず、全ての抽象 Verdier 列から実 fiber 列を得る。 -/
lemma abstractFiberTriangle_isFiber (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (hE.abstractFiberTriangle d) :=
  hE.fiberTriangle_isFiber (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d)

/-- 下辺は元の完全包含の像の同じ一単体。 -/
lemma abstractFiberTriangle_bottom (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (hE.abstractFiberTriangle d).square =
      SSet.yonedaEquiv.symm (E.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square ≫ E) = _
  rw [← Category.assoc, (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).bottom_edge]
  exact SSet.yonedaEquiv_symm_comp _ _

/-- 右辺は元の商関手の像の同じ一単体。 -/
lemma abstractFiberTriangle_right (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (hE.abstractFiberTriangle d).square =
      SSet.yonedaEquiv.symm (E.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square ≫ E) = _
  rw [← Category.assoc, (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).right_edge]
  exact SSet.yonedaEquiv_symm_comp _ _

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
