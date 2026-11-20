module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientValueSquare
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare

/-!
概要：元の二脚の実 cospan 上に、頂点が元の E(A) である候補の実 ∞ 錐を構成する。
方針：四辺固定の正方形を join 錐へ移し、右辺・上辺と左下の頂点を保持する。
規約：任意の可換実現からの候補で、極限性は主張しない。使われ方：d8 の比較錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
end SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
local instance coneSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

lemma square_source_vertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (square Φ p q i r h) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) := by
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (square Φ p q i r h)
  rw [square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1)
    (SSet.yonedaEquiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cSource Φ p q i)).edge)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cSource Φ p q i)).src_eq)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (square Φ p q i r h)

def cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cospan Φ p q i r h) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (square Φ p q i r h)

lemma cospan_C : horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cospan Φ p q i r h = SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, square_right]

lemma cospan_D : horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cospan Φ p q i r h = SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, square_top]

lemma cone_square : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cone Φ p q i r h) = square Φ p q i r h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare, Iso.inv_hom_id_assoc]

lemma cone_vertex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cone Φ p q i r h).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cone Φ p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.cone_square] at he
  exact he.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone.square_source_vertex Φ p q i r h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientValueCone

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
