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
    pastingTopTriangle (reverseGrid F) =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (pastingBottomTriangle F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

lemma exists_pasting_outer_limit_replacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hr : IsPullbackSquare (pastingSquare F 0))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : IsPullbackSquare S)
    (hbase : pushoutSpan (reverseGrid (pastingSquare F 1)) = pushoutSpan (reverseGrid S)) :
    ∃ F' : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      pastingSquare F' 0 = pastingSquare F 0 ∧
        pastingTopTriangle F' = pastingTopTriangle F ∧
        IsPullbackSquare (pastingSquare F' 2) ∧ pastingSquare F' 1 = S := by
  have hl : IsPushoutSquare (pastingSquare (reverseGrid F) 2) := by
    rw [reverseGrid_pastingSquare]
    exact (isPullbackSquare_iff_reverseGrid _).1 hr
  obtain ⟨G, hc, hg, ho⟩ := exists_pasting_outer_colimit_replacement (reverseGrid F) hl
    (reverseGrid S) ((isPullbackSquare_iff_reverseGrid S).1 hS)
    (by rw [reverseGrid_pastingSquare]; exact hbase)
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let F' := reverseGrid G ≫ q
  have hleft := pastingSquare_left_eq_of_corner_eq hc
  have hbottom := pastingBottomTriangle_eq_of_corner_eq hc
  refine ⟨F', ?_, ?_, ?_, ?_⟩
  · change pastingSquare (reverseGrid G) 0 ≫ q = _
    rw [reverseGrid_pastingSquare]
    change reverseGrid (pastingSquare G 2) ≫ q = _
    rw [hleft, reverseGrid_pastingSquare]
    exact reverseGrid_double (pastingSquare F 0)
  · have ht : pastingTopTriangle (reverseGrid G) =
        pastingTopTriangle (reverseGrid (reverseGrid F)) := by
      rw [reverseGrid_topTriangle, reverseGrid_topTriangle, hbottom]
    change pastingTopTriangle (reverseGrid G) ≫ q = _
    rw [ht]
    change pastingTopTriangle (reverseGrid (reverseGrid F) ≫ q) = _
    rw [reverseGrid_double]
  · change IsPullbackSquare (pastingSquare (reverseGrid G) 2 ≫ q)
    rw [reverseGrid_pastingSquare]
    exact (isPullbackSquare_iff_postcomp_isIso _ q).1
      ((isPushoutSquare_iff_reverseGrid _).1 hg)
  · change pastingSquare (reverseGrid G) 1 ≫ q = _
    rw [reverseGrid_pastingSquare]
    change reverseGrid (pastingSquare G 1) ≫ q = _
    rw [ho]
    exact reverseGrid_double S

structure PastingOuterLimitReplacement {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X
  right_eq : pastingSquare diagram 0 = pastingSquare F 0
  top_eq : pastingTopTriangle diagram = pastingTopTriangle F
  left_isPullback : IsPullbackSquare (pastingSquare diagram 2)
  outer_eq : pastingSquare diagram 1 = S

def pastingOuterLimitReplacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hr : IsPullbackSquare (pastingSquare F 0))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : IsPullbackSquare S)
    (hbase : pushoutSpan (reverseGrid (pastingSquare F 1)) = pushoutSpan (reverseGrid S)) :
    PastingOuterLimitReplacement F S := by
  let h := exists_pasting_outer_limit_replacement F hr S hS hbase
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1,
    h.choose_spec.2.2.1, h.choose_spec.2.2.2⟩

end SerrePositivity.KST.LocalizingInvariants
