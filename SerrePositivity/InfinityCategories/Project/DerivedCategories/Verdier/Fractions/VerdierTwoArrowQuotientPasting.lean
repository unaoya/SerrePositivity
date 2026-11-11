module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.LocalizingInvariants.TwoArrowCosliceNormalization
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.CosliceRoofPasting

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q}
  (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
  {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj} (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F)
  (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) (twoArrowCosliceEdge s)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget))

/-- 同じ実分数の指定 coslice 持ち上げ二単体。 -/
def twoArrowLiftedFractionTriangle : (Δ[2] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) := SSet.yonedaEquiv.symm r.lift.triangle.simplex

lemma twoArrowLiftedFractionTriangle_last : stdSimplex.δ (0 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s.lift := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  have h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)).δ (0 : Fin 3) r.lift.triangle.simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow s.lift).edge := r.lift.triangle.d₀
  rw [h₀, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s.lift)

/-- 元の全商四角形と同じ実右分数三角形を含む、指定合成三角柱。 -/
def verdierTwoArrowQuotientPasting : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism s.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last D L s r)

/-- 元の全商四角形は、同じ指定合成三角柱の元の面そのもの。 -/
lemma verdierTwoArrowQuotientPasting_original :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting D L s r) 0 =
      (β_ Δ[1] Δ[1]).hom ≫ F := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism_original, s.projection]

/-- 終端列は、同じ実分数で最初に回収した指定商合成二単体そのもの。 -/
lemma verdierTwoArrowQuotientPasting_top :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting D L s r) =
      SSet.yonedaEquiv.symm r.triangle.simplex := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism_top]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)).app (Opposite.op ⦋2⦌)
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle]
  rw [SSet.yonedaEquiv.apply_symm_apply]
  exact r.lift.triangle_image.trans
    (SSet.yonedaEquiv.apply_symm_apply r.triangle.simplex).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.twoArrowLiftedFractionTriangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.twoArrowLiftedFractionTriangle_last := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierTwoArrowQuotientPasting := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierTwoArrowQuotientPasting_original := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierTwoArrowQuotientPasting_top := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.twoArrowLiftedFractionTriangle._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.twoArrowLiftedFractionTriangle.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierTwoArrowQuotientPasting.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting.eq_1
