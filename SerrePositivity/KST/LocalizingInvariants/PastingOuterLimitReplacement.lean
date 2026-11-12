module

public import SerrePositivity.KST.LocalizingInvariants.PastingCornerPreservation

/-!
概要：右 pullback を含む長方形の外周を、指定した同じ cospan の極限へ取り替える。
方針：反対圏の余錐の厳密延長を二重反転で戻す。
規約：右正方形・上側合成三角形・外周正方形を保持。使われ方：元の E(A) の二脚の錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma reverseGrid_topTriangle {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

lemma exists_pasting_outer_limit_replacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare S)
    (hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid S)) :
    ∃ F' : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F' 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0 ∧
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F' = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F' 2) ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F' 1 = S := by
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) 2) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid _).1 hr
  obtain ⟨G, hc, hg, ho⟩ := exists_pasting_outer_colimit_replacement (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) hl
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid S) ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid S).1 hS)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]; exact hbase)
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let F' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G ≫ q
  have hleft := pastingSquare_left_eq_of_corner_eq hc
  have hbottom := pastingBottomTriangle_eq_of_corner_eq hc
  refine ⟨F', ?_, ?_, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) 0 ≫ q = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 2) ≫ q = _
    rw [hleft, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)
  · have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F)) := by
      rw [reverseGrid_topTriangle, reverseGrid_topTriangle, hbottom]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) ≫ q = _
    rw [ht]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) ≫ q) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) 2 ≫ q)
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_postcomp_isIso _ q).1
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_reverseGrid _).1 hg)
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) 1 ≫ q = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 1) ≫ q = _
    rw [ho]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double S

structure PastingOuterLimitReplacement {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X
  right_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0
  top_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle diagram = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F
  left_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2)
  outer_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 1 = S

def pastingOuterLimitReplacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare S)
    (hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid S)) :
    PastingOuterLimitReplacement F S := by
  let h := exists_pasting_outer_limit_replacement F hr S hS hbase
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1,
    h.choose_spec.2.2.1, h.choose_spec.2.2.2⟩

end SerrePositivity.KST.LocalizingInvariants
