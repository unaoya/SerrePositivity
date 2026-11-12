module
public import SerrePositivity.KST.SConstruction.InnerZeroBoundaryComparison

/-! # 全零境界商への比較の入力についての自然性
概要：内側の零列の商から全零境界商への点つき比較を自然変換に束ねる。
方針：自己関手の同型の入力についての自然性を実現へ移し、商射影の前で比較する。
規約：安定な入力の全ての射について厳密に自然。使われ方：点つき経路境界の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 概要：反復実現の座標同型は安定な入力の射について自然。
方針：自己関手の自然変換の入力についての自然性を core と対角で評価する。
規約：既存の座標同型そのもの。使われ方：境界商への比較の自然性。 -/
lemma iteratedSRealizationCoordinateIso_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealizationMap r f ≫ (iteratedSRealizationCoordinateIso r Y).hom =
      (iteratedSRealizationCoordinateIso r X).hom ≫ (multiRealizationFunctor (r + 1)).map f := by
  apply NatTrans.ext
  funext d
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  have h := ((diagonalSInnerComparisonNatIso r).hom.app d).naturality f
  have hh := congrArg H.map h
  simp only [CategoryTheory.Functor.map_comp] at hh
  exact NatTrans.congr_app hh d

/-- 概要：内側の零列の商から全零境界商への比較は入力について自然。
方針：商射影の前で座標同型の自然性に帰着する。
規約：点つき写像の厳密等号。使われ方：比較の自然変換への束ね。 -/
lemma innerZeroToFullBoundaryComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    reducedDiagonalMap (iteratedSRealizationDiagramMap r f) ≫
      innerZeroToFullBoundaryComparison r Y =
      innerZeroToFullBoundaryComparison r X ≫ boundaryReducedRealizationMap r f := by
  apply PointedObject.cofiber_hom_ext (diagonalZeroColumn (iteratedSRealizationDiagram r X))
  change diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫
      (reducedDiagonalMap (iteratedSRealizationDiagramMap r f)).right ≫
      (innerZeroToFullBoundaryComparison r Y).right =
    diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫
      (innerZeroToFullBoundaryComparison r X).right ≫ (boundaryReducedRealizationMap r f).right
  calc
    _ = iteratedSRealizationMap r f ≫
        diagonalReductionQuotient (iteratedSRealizationDiagram r Y) ≫
        (innerZeroToFullBoundaryComparison r Y).right := by
      rw [← Category.assoc, reducedDiagonalMap_quotient, Category.assoc]
      rfl
    _ = iteratedSRealizationMap r f ≫
        (iteratedSRealizationCoordinateIso r Y).hom ≫ boundaryReductionQuotient r Y := by
      rw [innerZeroToFullBoundaryComparison_quotient]
    _ = (iteratedSRealizationCoordinateIso r X).hom ≫
        (multiRealizationFunctor (r + 1)).map f ≫ boundaryReductionQuotient r Y := by
      rw [← Category.assoc, iteratedSRealizationCoordinateIso_naturality, Category.assoc]
    _ = (iteratedSRealizationCoordinateIso r X).hom ≫
        boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r f).right := by
      rw [boundaryReducedRealizationMap_quotient]
    _ = _ := by rw [← Category.assoc, ← innerZeroToFullBoundaryComparison_quotient, Category.assoc]

/-- 概要：全零境界商への点つき比較の自然変換。
方針：比較と入力の射についての自然性を束ねる。
規約：入力は安定な模型の圏。使われ方：点つき反復経路の自然な境界。 -/
def innerZeroToFullBoundaryComparisonNat (r : ℕ) :
    iteratedSRealizationDiagramFunctor.{u} r ⋙ reducedDiagonalFunctor ⟶
      boundaryReducedRealizationFunctor r where
  app := innerZeroToFullBoundaryComparison r
  naturality {_X _Y} f := innerZeroToFullBoundaryComparison_naturality r f

/-- 概要：全零境界商への比較を Kan 置換した自然変換。
方針：既存の点つき Kan 置換を後合成する。
規約：入力の射について厳密に自然。使われ方：Kan な標的の模型の比較。 -/
def innerZeroToFullBoundaryComparisonKanNat (r : ℕ) :
    (iteratedSRealizationDiagramFunctor.{u} r ⋙ reducedDiagonalFunctor) ⋙
        Spectra.PointedKanReplacement.functor ⟶ boundaryKanRealizationFunctor r :=
  Functor.whiskerRight (innerZeroToFullBoundaryComparisonNat r)
    Spectra.PointedKanReplacement.functor

/-- 概要：Kan 置換した比較は全基点・全自然数次数の π_* 同型。
方針：局所化での可逆性から既存の Kan 比較定理を使う。
規約：HT-KQ 等の追加仮定は不要。使われ方：反復実現の模型間の比較。 -/
lemma innerZeroToFullBoundaryComparisonKan_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (innerZeroToFullBoundaryComparison r X)).right :=
  pointedKanReplacement_map_piIsomorphism_of_localized_isIso (innerZeroToFullBoundaryComparison r X)
    (innerZeroToFullBoundaryComparison_image_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) r X)

end SerrePositivity.KST.SConstruction
