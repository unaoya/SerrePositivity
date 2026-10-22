module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationPrism
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.Derived.PinchedSliceTransport

/-!
# 元の corner 評価の任意パラメータ上の実合成三角形

概要：元の corner を任意の族で制限しても、同じ実 prism から全関手圏の三角形を得る。
方針：同じ qY slice の実ホモトピーと普遍錐評価を三辺の全円柱へ移す。
規約：全パラメータを保ち、左脚の標準自然変換との照合は別工程。
使われ方：実 ProductHomMap 側の全三角形の幾何的構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [LeftFibration (roofTargetProjection A Y q)]
  {S : SSet.{u}} (f : S ⟶ sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q))

def roofCornerEvaluationRightHomotopy : SSet.Homotopy
    ((f ≫ roofCornerSourceSliceMap A Y q b) ≫
      sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))))
    (SSet.const (X := S) (q.app (op ⦋0⦌) (nerveVertex Y))) :=
  stableHomotopyRetarget (functorHomotopyPrecomp
    (roofSliceEvaluationHomotopy (q.app (op ⦋0⦌) (nerveVertex Y)))
    (f ≫ roofCornerSourceSliceMap A Y q b)) rfl (SSet.comp_const _ _)

def roofCornerEvaluationLeftHomotopy : SSet.Homotopy
    ((f ≫ roofCornerSourceSliceMap A Y q b) ≫
      sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))))
    (SSet.const (X := S)
      (q.app (op ⦋0⦌) (nerveVertex (A.obj (roofTargetDegree A Y q b))))) := by
  let H := functorHomotopyPostcomp
    (functorHomotopyPrecomp (roofCornerEvaluationSliceHomotopy A Y q b) f)
    (sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))))
  apply stableHomotopyRetarget H rfl
  rw [Category.assoc, Category.assoc, pinchedFamilySlice_projection, SSet.comp_const,
    SSet.comp_const]

lemma roofCornerEvaluation_triangle :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (roofCornerEvaluationLeftHomotopy A Y q b f)) ≫
      intervalFamilyHom ((f ≫ roofCornerEvaluation A Y q b) ≫
        pinchedHomToIntervalMappingSpace _ _) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (roofCornerEvaluationRightHomotopy A Y q b f)) := by
  let H := functorHomotopyPrecomp (roofCornerEvaluationSliceHomotopy A Y q b) f
  let P := (β_ (Δ[1] : SSet.{u}) S).hom ≫ H.h
  have h₀ : prismEndpoint 0 S ≫ P = f ≫ roofCornerSourceSliceMap A Y q b := by
    change SSet.ι₀ ≫ H.h = _
    exact H.h₀
  have h₁ : prismEndpoint 1 S ≫ P = (f ≫ roofCornerEvaluation A Y q b) ≫
      pinchedFamilySlice E
        (q.app (op ⦋0⦌) (nerveVertex (A.obj (roofTargetDegree A Y q b))))
        (q.app (op ⦋0⦌) (nerveVertex Y)) := by
    change SSet.ι₁ ≫ H.h = _
    exact H.h₁.trans (Category.assoc _ _ _).symm
  apply slicePrismFamily_comp (q.app (op ⦋0⦌) (nerveVertex Y))
    (roofCornerEvaluationLeftHomotopy A Y q b f)
    (roofCornerEvaluationRightHomotopy A Y q b f)
    (intervalFamilyHomotopy ((f ≫ roofCornerEvaluation A Y q b) ≫
      pinchedHomToIntervalMappingSpace _ _)) P
  · rw [h₀]
    exact (roofSliceEvaluationHomotopy_precomp_h _ _).symm
  · rw [h₁]
    exact (roofSliceEvaluationHomotopy_precomp_h _ _).symm.trans
      (roofSliceEvaluationHomotopy_pinched_h (f ≫ roofCornerEvaluation A Y q b))
  · change (β_ S (Δ[1] : SSet.{u})).hom ≫
      ((β_ (Δ[1] : SSet.{u}) S).hom ≫ H.h) ≫ _ = _
    simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    rfl

lemma roofCornerEvaluation_triangle_retarget (d : S ⟶ E)
    (hd : (f ≫ roofCornerSourceSliceMap A Y q b) ≫
      sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))) = d) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (stableHomotopyRetarget (roofCornerEvaluationLeftHomotopy A Y q b f) hd rfl)) ≫
      intervalFamilyHom ((f ≫ roofCornerEvaluation A Y q b) ≫
        pinchedHomToIntervalMappingSpace _ _) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (stableHomotopyRetarget (roofCornerEvaluationRightHomotopy A Y q b f) hd rfl)) := by
  subst d
  exact roofCornerEvaluation_triangle A Y q b f

end SerrePositivity.EInfinity.FrameHom.FrameArrows
