module

public import SerrePositivity.KST.LocalizingInvariants.CosliceRoofPasting

/-!
概要：回収済みの同じ実右分数を、元の商四角形を保つ合成三角柱へ実代入する。
方針：指定 coslice 持ち上げ三角形の後辺一致を証明し、全貼合せを射影する。
規約：元の商四角形・実分数・持ち上げ三角形を選び直さず、全二胞体を保持する。
使われ方：二つの実四角形の商像と、元の単体関手上の指定合成との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q}
  (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
  {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj} (s : SquareCosliceSeed F)
  (r : VerdierCosliceFractionNormalization h (fractionSquarePoint F) (twoArrowCosliceEdge s)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget))

/-- 同じ実分数の指定 coslice 持ち上げ二単体。 -/
def twoArrowLiftedFractionTriangle : (Δ[2] : SSet.{u}) ⟶
    sliceUnder (fractionSquarePoint F) := SSet.yonedaEquiv.symm r.lift.triangle.simplex

lemma twoArrowLiftedFractionTriangle_last : stdSimplex.δ (0 : Fin 3) ≫
    twoArrowLiftedFractionTriangle D L s r = squareRightEdge ≫ s.lift := by
  rw [twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  have h₀ : (sliceUnder (fractionSquarePoint F)).δ (0 : Fin 3) r.lift.triangle.simplex =
      (squareRightArrow s.lift).edge := r.lift.triangle.d₀
  rw [h₀, squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply (squareRightEdge ≫ s.lift)

/-- 元の全商四角形と同じ実右分数三角形を含む、指定合成三角柱。 -/
def verdierTwoArrowQuotientPasting : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj :=
  roofPastingPrism s.lift (twoArrowLiftedFractionTriangle D L s r)
    (twoArrowLiftedFractionTriangle_last D L s r)

/-- 元の全商四角形は、同じ指定合成三角柱の元の面そのもの。 -/
lemma verdierTwoArrowQuotientPasting_original :
    pastingSquare (verdierTwoArrowQuotientPasting D L s r) 0 =
      (β_ Δ[1] Δ[1]).hom ≫ F := by
  rw [verdierTwoArrowQuotientPasting, roofPastingPrism_original, s.projection]

/-- 終端列は、同じ実分数で最初に回収した指定商合成二単体そのもの。 -/
lemma verdierTwoArrowQuotientPasting_top :
    pastingTopTriangle (verdierTwoArrowQuotientPasting D L s r) =
      SSet.yonedaEquiv.symm r.triangle.simplex := by
  rw [verdierTwoArrowQuotientPasting, roofPastingPrism_top]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (sliceUnderProjection (fractionSquarePoint F)).app (Opposite.op ⦋2⦌)
    (SSet.yonedaEquiv (twoArrowLiftedFractionTriangle D L s r)) = _
  rw [twoArrowLiftedFractionTriangle]
  rw [SSet.yonedaEquiv.apply_symm_apply]
  exact r.lift.triangle_image.trans
    (SSet.yonedaEquiv.apply_symm_apply r.triangle.simplex).symm

end SerrePositivity.KST.LocalizingInvariants
