module

public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactMapHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-!
概要：任意の抽象 Verdier 列の coherent 四角形による提示。
方針：零化の関手同型から StableInfinity の可換四辺を得て、実際の四角形を選ぶ。
規約：元の包含・商と零安定圏を保持する。使われ方：局所化不変量の非空な入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 包含・商・零角を経由する二辺を全て固定した、実際の四角形。 -/
lemma exists_verdierSquare (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    ∃ Q : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory d.right)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory d.right)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).toTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).toTruncated
  have hi := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) d.inclusion d.projection).toTruncated
  have hz := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left) (fromZeroCategory d.right)).toTruncated
  let F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right := ⟨d.inclusion.hom ≫ d.projection.hom, inferInstance⟩
  let G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right :=
    ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left).hom ≫ (fromZeroCategory d.right).hom, inferInstance⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom := verdierZeroCompositeIso d
  have hh := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrow_homMk_eq_of_functorIso
    (F := F) (G := G) he
  exact hi.trans (hh.trans hz.symm)

/-- 選択した四角形は元の Verdier 列と四辺を保持する。 -/
def VerdierSequence.presentation (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u} := by
  let Q := Classical.choose (exists_verdierSquare d)
  have hQ := Classical.choose_spec (exists_verdierSquare d)
  have h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.left := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source Q
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).src_eq] at h
    exact h.symm
  have h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 1 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.middle := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target Q
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).tgt_eq] at h
    exact h.symm
  have h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.right := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target Q
    rw [hQ.2.2.2, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).tgt_eq] at h
    exact h.symm
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target Q
    rw [hQ.2.2.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).tgt_eq] at h
    exact h.symm
  exact {
    toVerdierSequence := d
    square := Q
    left_eq := h₀
    middle_eq := h₁
    right_eq := h₂
    bottom_edge := hQ.1
    right_edge := hQ.2.2.2
    zero_corner := by rw [hz, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]; exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero }

lemma VerdierSequence.presentation_sequence (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).toVerdierSequence = d := rfl

lemma VerdierSequence.presentation_left (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).edge :=
  (Classical.choose_spec (exists_verdierSquare d)).2.2.1

lemma VerdierSequence.presentation_top (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation d).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory d.right)).edge :=
  (Classical.choose_spec (exists_verdierSquare d)).2.1

end SerrePositivity.KST.LocalizingInvariants
