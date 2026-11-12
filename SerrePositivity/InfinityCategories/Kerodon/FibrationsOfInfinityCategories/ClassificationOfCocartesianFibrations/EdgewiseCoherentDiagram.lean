module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso

/-!
概要：一般の coherent な空間値図式を edgewise な Hom の共通解像へ移す。
方針：右端射影の coherent nerve の同値の逆で図式を移し、対象の解像の族で置き換える。
規約：通常の図式に制限せず、元の図式との比較を関手空間の同型として保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の自然な比較を一般の図式に適用する準備。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：任意の coherent な空間値図式を Hom の edgewise 解像の coherent nerve へ移す。
方針：元の対象への右端射影の同値の逆を後合成する。
規約：比較を伴う非計算的な持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Hom のパラメーターを解像した族に図式を移す。 -/
noncomputable def edgewiseCoherentDiagramLift {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    B ⟶ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :=
  F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).inv

/-- 概要：共通解像に移した図式を右端射影で戻すと元の図式と関手同型。
方針：同値の逆と順方向の合成の比較を元の図式で引き戻す。
規約：底 B に quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共通解像上の図式と元の図式の接続。 -/
noncomputable def edgewiseCoherentDiagramLiftIso {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (edgewiseCoherentDiagramLift F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) F := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).invHomIso.precomp F
  simp only [Category.comp_id, ← Category.assoc] at h
  exact h

/-- 概要：一般の coherent な空間値図式を対象の edgewise 解像の族で置き換える。
方針：共通解像へ移した図式に対象の解像の豊穣作用の coherent nerve を後合成する。
規約：元の図式の高次の Hom の情報も移送する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の比較に使う共通の対象の図式。 -/
noncomputable def edgewiseCoherentReplacement {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := edgewiseCoherentDiagramLift F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanInfinityMap

/-- 概要：edgewise 解像による一般の図式の置き換えは元の図式と関手同型。
方針：対象の解像の族と元の対象の族の比較を共通解像上の図式で引き戻す。
規約：単なる対象ごとの同値ではなく図式全体の関手同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式の比較を共通解像上で証明する。 -/
noncomputable def edgewiseCoherentReplacementIso {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (edgewiseCoherentReplacement F) F := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanInfinityComparisonIso.precomp (edgewiseCoherentDiagramLift F)
  exact h ≪≫ edgewiseCoherentDiagramLiftIso F

/-- 概要：edgewise に置き換えた一般の図式の小さい unstraightening は元のものと同値。
方針：図式全体の関手同型に小さい unstraightening の同値不変性を適用する。
規約：底は任意の小さい quasicategory。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共通解像上で証明する全空間の比較を元へ戻す。 -/
noncomputable def smallEdgewiseCoherentReplacementEquivalence {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (edgewiseCoherentReplacement F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningEquivalenceOfFunctorIso (edgewiseCoherentReplacementIso F)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
