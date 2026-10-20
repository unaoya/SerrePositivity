module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteOreCompositionHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionHomotopy
public import SerrePositivity.InfinityCategories.Derived.HomotopyCompositionRelativeOver

/-! # 有限実 Ore 細分の同じ対角を持つ実三角形族

概要：実 Ore 比較と第二合成 prism を貼り、第一合成 prism と同じ対角からの族を得る。
方針：slice 射影上で底に定値な Ore 比較を、指定底三角形を保って合成する。
規約：元の実比較と二合成 prism を変更しない。使われ方：実屋根合成の四三角形の族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} {x y z : D}
variable {f : K ⟶ DGNerve.pinchedHom A D x y}
variable {s : ForgetEnrichment.of (Complex A) z ⟶ ForgetEnrichment.of (Complex A) y}
variable (R : DGFiniteOreRefinement A D P f s)

/-- 実 Ore 細分の第一三角形族は、元の指定分母と分子の同じ実合成 prism。 -/
def DGFiniteOreRefinement.firstTriangleHomotopy : SSet.Homotopy
    (pinchedHomCompositionFamily (SSet.const (pinchedClosedVertex A D R.combinedDenominator)) f ≫
      dgPinchedHomSlice A D R.refinedSource y)
    (f ≫ dgPinchedHomSlice A D x y) :=
  dgPinchedCompositionFamilyHomotopy A D
    (SSet.const (pinchedClosedVertex A D R.combinedDenominator)) f

/-- 同じ実対角からの第二三角形族と、元の Ore 比較・第二 prism との実合成三角形。 -/
structure DGFiniteOreTrianglePrisms where
  second : SSet.Homotopy
    (pinchedHomCompositionFamily (SSet.const (pinchedClosedVertex A D R.combinedDenominator)) f ≫
      dgPinchedHomSlice A D R.refinedSource y)
    (SSet.const (pinchedClosedVertex A D s) ≫ dgPinchedHomSlice A D z y)
  comparisonTriangle : FunctorCompositionTriangle
    (functorHomotopyPostcomp R.compositionHomotopy (dgPinchedHomSlice A D R.refinedSource y))
    (dgPinchedCompositionFamilyHomotopy A D R.lift (SSet.const (pinchedClosedVertex A D s))) second
  triangle_over : comparisonTriangle.diagram ≫
      (ihom K).map (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))) =
    functorIdentityCompositionDiagram (functorHomotopyPostcomp
      (dgPinchedCompositionFamilyHomotopy A D R.lift (SSet.const (pinchedClosedVertex A D s)))
      (sliceOverProjection ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))))
  second_over : second.h ≫ sliceOverProjection _ =
    (dgPinchedCompositionFamilyHomotopy A D R.lift
      (SSet.const (pinchedClosedVertex A D s))).h ≫ sliceOverProjection _

/-- 元の実 Ore 比較は、実 slice の始域射影で全時刻定値となる。 -/
lemma DGFiniteOreRefinement.comparisonSlice_over :
    (R.compositionHomotopy.h ≫ dgPinchedHomSlice A D R.refinedSource y) ≫
        sliceOverProjection _ =
      fst K (Δ[1] : SSet.{max u v}) ≫
        (pinchedHomCompositionFamily R.lift (SSet.const (pinchedClosedVertex A D s)) ≫
          dgPinchedHomSlice A D R.refinedSource y) ≫ sliceOverProjection _ := by
  have hc := dgPinchedHomSlice_projection A D R.refinedSource y
  have hL := congrArg (fun k => R.compositionHomotopy.h ≫ k) hc
  have hR := congrArg (fun k => fst K (Δ[1] : SSet.{max u v}) ≫
    pinchedHomCompositionFamily R.lift (SSet.const (pinchedClosedVertex A D s)) ≫ k) hc
  exact (hL.trans (SSet.comp_const _ _)).trans (hR.trans (SSet.comp_const _ _)).symm

/-- 実 Ore 細分は、同じ対角・指定底を持ち、元の比較を保持する実三角形族を供給する。 -/
theorem dgFiniteOreTrianglePrisms_nonempty : Nonempty (DGFiniteOreTrianglePrisms A D P R) := by
  let p := sliceOverProjection
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))
  let l := functorHomotopyPostcomp R.compositionHomotopy
    (dgPinchedHomSlice A D R.refinedSource y)
  let r := dgPinchedCompositionFamilyHomotopy A D R.lift
    (SSet.const (pinchedClosedVertex A D s))
  have hl := R.comparisonSlice_over
  obtain ⟨d, T, hT, hd⟩ := homotopyCompositionOver_fixedLeft_exists p l r hl
  exact ⟨⟨d, T, hT, hd⟩⟩

/-- 任意の指定部分上の全比較三角形を保って、同じ底を持つ共通対角の三角形族へ延長する。 -/
theorem dgFiniteOreTrianglePrisms_relative_exists {L : SSet.{max u v}}
    (i : L ⟶ K) [Mono i]
    (DA : (Δ[2] : SSet.{max u v}) ⟶ (ihom L).obj
      (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))))
    (h₀A : stdSimplex.δ (0 : Fin 3) ≫ DA = curry
      (dgPinchedCompositionFamilyHomotopy A D R.lift
        (SSet.const (pinchedClosedVertex A D s))).h ≫ (pre i).app _)
    (h₂A : stdSimplex.δ (2 : Fin 3) ≫ DA = curry
      (R.compositionHomotopy.h ≫ dgPinchedHomSlice A D R.refinedSource y) ≫ (pre i).app _)
    (hc : DA ≫ (ihom L).map (sliceOverProjection _) =
      functorIdentityCompositionDiagram (functorHomotopyPostcomp
        (dgPinchedCompositionFamilyHomotopy A D R.lift
          (SSet.const (pinchedClosedVertex A D s)))
        (sliceOverProjection
          ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))) ≫
          (pre i).app (dgNerve A D)) :
    ∃ C : DGFiniteOreTrianglePrisms A D P R,
      C.comparisonTriangle.diagram ≫ (pre i).app _ = DA := by
  let p := sliceOverProjection
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))
  let l := functorHomotopyPostcomp R.compositionHomotopy
    (dgPinchedHomSlice A D R.refinedSource y)
  let r := dgPinchedCompositionFamilyHomotopy A D R.lift
    (SSet.const (pinchedClosedVertex A D s))
  obtain ⟨d, T, hA, hB, hd⟩ := homotopyCompositionRelativeOver_fixedLeft_exists
    i p l r R.comparisonSlice_over DA h₀A h₂A hc
  exact ⟨⟨d, T, hB, hd⟩, hA⟩

end SerrePositivity.InfinityCategories
