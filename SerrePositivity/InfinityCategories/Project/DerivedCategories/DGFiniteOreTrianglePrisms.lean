module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreCompositionHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedCompositionHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HomotopyCompositionRelativeOver

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} {x y z : D}
variable {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y}
variable {s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteOreRefinement A D P f s)

/-- 実 Ore 細分の第一三角形族は、元の指定分母と分子の同じ実合成 prism。 -/
def DGFiniteOreRefinement.firstTriangleHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.combinedDenominator)) f ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y)
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.combinedDenominator)) f

/-- 同じ実対角からの第二三角形族と、元の Ore 比較・第二 prism との実合成三角形。 -/
structure DGFiniteOreTrianglePrisms where
  second : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.combinedDenominator)) f ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D z y)
  comparisonTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp R.compositionHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))) second
  triangle_over : comparisonTriangle.diagram ≫
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))))
  second_over : second.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _

/-- 元の実 Ore 比較は、実 slice の始域射影で全時刻定値となる。 -/
lemma DGFiniteOreRefinement.comparisonSlice_over :
    (R.compositionHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      fst K (Δ[1] : SSet.{max u v}) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily R.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice_projection A D R.refinedSource y
  have hL := congrArg (fun k => R.compositionHomotopy.h ≫ k) hc
  have hR := congrArg (fun k => fst K (Δ[1] : SSet.{max u v}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily R.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)) ≫ k) hc
  exact (hL.trans (SSet.comp_const _ _)).trans (hR.trans (SSet.comp_const _ _)).symm

/-- 実 Ore 細分は、同じ対角・指定底を持ち、元の比較を保持する実三角形族を供給する。 -/
theorem dgFiniteOreTrianglePrisms_nonempty : Nonempty (DGFiniteOreTrianglePrisms A D P R) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  let l := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp R.compositionHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y)
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))
  have hl := R.comparisonSlice_over
  obtain ⟨d, T, hT, hd⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.homotopyCompositionOver_fixedLeft_exists p l r hl
  exact ⟨⟨d, T, hT, hd⟩⟩

/-- 任意の指定部分上の全比較三角形を保って、同じ底を持つ共通対角の三角形族へ延長する。 -/
theorem dgFiniteOreTrianglePrisms_relative_exists {L : SSet.{max u v}}
    (i : L ⟶ K) [Mono i]
    (DA : (Δ[2] : SSet.{max u v}) ⟶ (ihom L).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))))
    (h₀A : stdSimplex.δ (0 : Fin 3) ≫ DA = curry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))).h ≫ (pre i).app _)
    (h₂A : stdSimplex.δ (2 : Fin 3) ≫ DA = curry
      (R.compositionHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y) ≫ (pre i).app _)
    (hc : DA ≫ (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift
          (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))) ≫
          (pre i).app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) :
    ∃ C : DGFiniteOreTrianglePrisms A D P R,
      C.comparisonTriangle.diagram ≫ (pre i).app _ = DA := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  let l := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp R.compositionHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D R.refinedSource y)
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D R.lift
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))
  obtain ⟨d, T, hA, hB, hd⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyCompositionRelativeOver_fixedLeft_exists
    i p l r R.comparisonSlice_over DA h₀A h₂A hc
  exact ⟨⟨d, T, hB, hd⟩, hA⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
