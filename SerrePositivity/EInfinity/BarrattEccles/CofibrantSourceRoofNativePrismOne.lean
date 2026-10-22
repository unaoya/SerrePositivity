module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismOne
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinchedValue
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrism
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationPinched

/-!
# 元の実 native prism の一端は同じ native pinched 族

概要：同じ全混合単体の一端を元の native pinched 族の slice 表示へ厳密に同定する。
方針：coherent Hom 比較の全単体の式と元の端点輸送の値の不変性を使う。
規約：任意可換環・同じ qD_n と qY・元の全パラメータを保持する。
使われ方：native roof 全三角形の一端条件 ht。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaNativeSimplex_one {n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b) :
    cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ (OrderHom.const _ 1) =
    coherentHomComparisonSimplex
      (C := KanHammockCategory (cofibrantAlgebraRelativeCategory A))
      (X := (kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
        (show (cofibrantAlgebraRelativeCategory A).category from
          cofibrantSourceRoofDegreeAlgebra A X Y b))
      (Y := (kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
        (show (cofibrantAlgebraRelativeCategory A).category from Y))
      ((cofibrantSourceRoofProductCommaNativeFamilyMap A X Y b).app (Opposite.op ⦋n⦌) Γ) :=
  RoofPrefix.simplex_one (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ

lemma cofibrantSourceRoofProductCommaNativePinchedMap_app_val {n : ℕ}
    (Γ : (nerve (cofibrantSourceRoofProductComma A X Y b)) _⦋n⦌) :
    ((cofibrantSourceRoofProductCommaNativePinchedMap A X Y b).app (Opposite.op ⦋n⦌) Γ).val =
    coherentHomComparisonSimplex
      (C := KanHammockCategory (cofibrantAlgebraRelativeCategory A))
      (X := (kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
        (show (cofibrantAlgebraRelativeCategory A).category from
          cofibrantSourceRoofDegreeAlgebra A X Y b))
      (Y := (kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).obj
        (show (cofibrantAlgebraRelativeCategory A).category from Y))
      ((cofibrantSourceRoofProductCommaNativeFamilyMap A X Y b).app (Opposite.op ⦋n⦌) Γ) := by
  rw [← cofibrantSourceRoofProductCommaNativeFamilyMap_pinched A X Y b]
  exact kanHammockHomPinchedMap_app_val (cofibrantAlgebraRelativeCategory A)
    (show (cofibrantAlgebraRelativeCategory A).category from
      cofibrantSourceRoofDegreeAlgebra A X Y b)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    ((cofibrantSourceRoofProductCommaNativeFamilyMap A X Y b).app (Opposite.op ⦋n⦌) Γ)

lemma cofibrantSourceRoofProductCommaNativePrism_one :
    prismEndpoint 1 (nerve (cofibrantSourceRoofProductComma A X Y b)) ≫
      cofibrantSourceRoofProductCommaNativePrism A X Y b =
    cofibrantSourceRoofProductCommaNativePinchedMap A X Y b ≫
      pinchedFamilySlice (kanHammockNerve (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
        (cofibrantHammockVertex A Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ (OrderHom.const _ 1)) =
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (((cofibrantSourceRoofProductCommaNativePinchedMap A X Y b).app
          (Opposite.op ⦋n⦌) Γ).val)
  rw [cofibrantSourceRoofProductCommaNativeSimplex_one A X Y b Γ,
    cofibrantSourceRoofProductCommaNativePinchedMap_app_val A X Y b Γ]

lemma cofibrantSourceRoofProductCommaNativePrism_one_evaluation :
    (β_ (nerve (cofibrantSourceRoofProductComma A X Y b)) (Δ[1] : SSet.{u + 1})).hom ≫
      rightMappingSpacePrism _ ≫ sliceOverUncurry
        (prismEndpoint 1 _ ≫ cofibrantSourceRoofProductCommaNativePrism A X Y b) =
    (intervalFamilyHomotopy (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b ≫
      pinchedHomToIntervalMappingSpace _ _)).h := by
  rw [cofibrantSourceRoofProductCommaNativePrism_one A X Y b]
  exact (roofSliceEvaluationHomotopy_precomp_h (cofibrantHammockVertex A Y)
    (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b ≫
      pinchedFamilySlice _ _ _)).symm.trans
        (roofSliceEvaluationHomotopy_pinched_h
          (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b))

end SerrePositivity.EInfinity.BarrattEccles
