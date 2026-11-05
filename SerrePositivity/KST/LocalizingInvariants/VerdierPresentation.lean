module

public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactMapHomotopy
public import SerrePositivity.InfinityCategories.Core.CommutativeSquareRealization

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
lemma exists_verdierSquare (d : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u}) :
    ∃ Q : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u},
      squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.inclusion).edge ∧
      squareTopEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (fromZeroCategory d.right)).edge ∧
      squareLeftEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left)).edge ∧
      squareRightEdge ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.projection).edge := by
  apply exists_stableSquare_of_homMk_comm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.inclusion).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (fromZeroCategory d.right)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left)).toTruncated (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.projection).toTruncated
  have hi := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) d.inclusion d.projection).toTruncated
  have hz := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u})
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left) (fromZeroCategory d.right)).toTruncated
  let F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap d.left d.right := ⟨d.inclusion.hom ≫ d.projection.hom, inferInstance⟩
  let G : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap d.left d.right :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left).hom ≫ (fromZeroCategory d.right).hom, inferInstance⟩
  have he : FunctorIso F.hom G.hom := verdierZeroCompositeIso d
  have hh := _root_.SerrePositivity.InfinityCategories.Stable.Exact.stableArrow_homMk_eq_of_functorIso
    (F := F) (G := G) he
  exact hi.trans (hh.trans hz.symm)

/-- 選択した四角形は元の Verdier 列と四辺を保持する。 -/
def VerdierSequence.presentation (d : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u} := by
  let Q := Classical.choose (exists_verdierSquare d)
  have hQ := Classical.choose_spec (exists_verdierSquare d)
  have h₀ : squareVertex Q 0 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex d.left := by
    have h := squareBottomEdge_source Q
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.inclusion).src_eq] at h
    exact h.symm
  have h₁ : squareVertex Q 1 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex d.middle := by
    have h := squareBottomEdge_target Q
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.inclusion).tgt_eq] at h
    exact h.symm
  have h₂ : squareVertex Q 1 1 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex d.right := by
    have h := squareRightEdge_target Q
    rw [hQ.2.2.2, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow d.projection).tgt_eq] at h
    exact h.symm
  have hz : squareVertex Q 0 1 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory.{u} := by
    have h := squareLeftEdge_target Q
    rw [hQ.2.2.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left)).tgt_eq] at h
    exact h.symm
  exact {
    toVerdierSequence := d
    square := Q
    left_eq := h₀
    middle_eq := h₁
    right_eq := h₂
    bottom_edge := hQ.1
    right_edge := hQ.2.2.2
    zero_corner := by rw [hz, _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject_vertex]; exact zeroCategory_isZero }

lemma VerdierSequence.presentation_sequence (d : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u}) :
    d.presentation.toVerdierSequence = d := rfl

lemma VerdierSequence.presentation_left (d : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u}) :
    squareLeftEdge ≫ d.presentation.square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory d.left)).edge :=
  (Classical.choose_spec (exists_verdierSquare d)).2.2.1

lemma VerdierSequence.presentation_top (d : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u}) :
    squareTopEdge ≫ d.presentation.square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (fromZeroCategory d.right)).edge :=
  (Classical.choose_spec (exists_verdierSquare d)).2.1

end SerrePositivity.KST.LocalizingInvariants
