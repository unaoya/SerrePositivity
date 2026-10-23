module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedArrowPrismBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.RightTensorCurryMap

/-!
概要：両全境界を固定した円柱を、同じ全図式の余錐の固定境界 fiber へ移す。
方針：区間の curry の制限自然性で両固定条件を運び、実 fiber に持ち上げる。
規約：全パラメーターで両固定条件を保持。使われ方：元の q の全変換の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {T X : SSet.{u}} (a : T ⊗ (Δ[1] : SSet.{u}) ⟶ X)
  (d : (Δ[1] : SSet.{u}) ⟶ X)

/-- 両指定全境界を固定した実円柱 fiber の元の関手空間への包含。 -/
def fixedArrowPrismBoundaryInclusion : fixedArrowPrismBoundary a d ⟶
    (ihom (join T (Δ[0] : SSet.{u}) ⊗ Δ[1])).obj X :=
  vertexFiberι (arrowPrismBoundaryRestriction T X)
    (functorVertex a, functorVertex (snd (Δ[0] : SSet.{u}) Δ[1] ≫ d))

/-- 同じ実 fiber の試験族側の全境界は元の a に定値。 -/
lemma fixedArrowPrismBoundaryInclusion_old : fixedArrowPrismBoundaryInclusion a d ≫
    (pre (joinInl T (Δ[0] : SSet.{u}) ▷ Δ[1])).app X = SSet.const (functorVertex a) := by
  have h := congrArg (fun f ↦ f ≫ fst _ _) (vertexFiberι_comp
    (arrowPrismBoundaryRestriction T X)
    (functorVertex a, functorVertex (snd (Δ[0] : SSet.{u}) Δ[1] ≫ d)))
  simp only [Category.assoc, arrowPrismBoundaryRestriction, lift_fst, SSet.const_comp] at h
  exact h

/-- 同じ実 fiber の頂点側の全境界は指定区間 d に定値。 -/
lemma fixedArrowPrismBoundaryInclusion_tip : fixedArrowPrismBoundaryInclusion a d ≫
    (pre (joinInr T (Δ[0] : SSet.{u}) ▷ Δ[1])).app X =
      SSet.const (functorVertex (snd (Δ[0] : SSet.{u}) Δ[1] ≫ d)) := by
  have h := congrArg (fun f ↦ f ≫ snd _ _) (vertexFiberι_comp
    (arrowPrismBoundaryRestriction T X)
    (functorVertex a, functorVertex (snd (Δ[0] : SSet.{u}) Δ[1] ≫ d)))
  simp only [Category.assoc, arrowPrismBoundaryRestriction, lift_snd, SSet.const_comp] at h
  exact h

/-- 区間を curry した同じ指定頂点は、元の d を表す点写像そのもの。 -/
lemma rightTensorCurry_point :
    curry ((β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫ snd (Δ[0] : SSet.{u}) Δ[1] ≫ d) =
      SSet.yonedaEquiv.symm (functorVertex d) := by
  apply uncurry_injective
  rw [uncurry_curry, SSet.yonedaEquiv_symm_zero, uncurry_const_functorVertex,
    braiding_hom_snd_assoc]

/-- 両境界の固定条件を保つ、円柱から全図式の余錐への実際の curry。 -/
def fixedArrowPrismBoundaryCurry : fixedArrowPrismBoundary a d ⟶
    fixedCoconeBoundary (SSet.yonedaEquiv.symm (functorVertex d))
      (curry ((β_ (Δ[1] : SSet.{u}) T).hom ≫ a)) :=
  vertexFiberLift _ _ (fixedArrowPrismBoundaryInclusion a d ≫
    rightTensorCurryMap (join T (Δ[0] : SSet.{u})) Δ[1] X) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, coconeBoundaryPairRestriction, lift_fst, SSet.const_comp]
        change fixedArrowPrismBoundaryInclusion a d ≫
          rightTensorCurryMap (join T Δ[0]) Δ[1] X ≫ (pre (joinInl T Δ[0])).app _ =
            SSet.const (functorVertex (curry ((β_ (Δ[1] : SSet.{u}) T).hom ≫ a)))
        rw [← rightTensorCurryMap_source, ← Category.assoc,
          fixedArrowPrismBoundaryInclusion_old, SSet.const_comp, rightTensorCurryMap_vertex]
      · simp only [Category.assoc, coconeBoundaryPairRestriction, lift_snd, SSet.const_comp]
        change fixedArrowPrismBoundaryInclusion a d ≫
          rightTensorCurryMap (join T Δ[0]) Δ[1] X ≫ (pre (joinInr T Δ[0])).app _ =
            SSet.const (functorVertex (SSet.yonedaEquiv.symm (functorVertex d)))
        rw [← rightTensorCurryMap_source, ← Category.assoc,
          fixedArrowPrismBoundaryInclusion_tip, SSet.const_comp,
          rightTensorCurryMap_vertex, rightTensorCurry_point])

/-- 元の関手空間へ含めると、同じ円柱の curry 自体を回収する。 -/
lemma fixedArrowPrismBoundaryCurry_ι : fixedArrowPrismBoundaryCurry a d ≫
    vertexFiberι (coconeBoundaryPairRestriction T ((ihom (Δ[1] : SSet.{u})).obj X))
      (functorVertex (curry ((β_ (Δ[1] : SSet.{u}) T).hom ≫ a)),
        functorVertex (SSet.yonedaEquiv.symm (functorVertex d))) =
      fixedArrowPrismBoundaryInclusion a d ≫
        rightTensorCurryMap (join T (Δ[0] : SSet.{u})) Δ[1] X :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
