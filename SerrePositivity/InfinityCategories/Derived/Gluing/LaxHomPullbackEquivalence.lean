module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomCoordinateTargetIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackKanComplex
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputPathEquivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
/-!
概要：正本 lax Hom 比較そのものの実ホモトピー同値性を証明する。
方針：元二入力を保つ実標的輸送と四座標同型を後合成し、既存の同値と厳密に照合して相殺する。
規約：公開正本比較・全二三角形・元左右 Hom 入力を保持し、追加仮定を置かない。
使われ方：比較の実逆射と両往復変形、充満忠実性と ∞ 普遍性を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomPullbackComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomPullbackComparison R C D M X Y) := by
  letI := dgGluingLaxHomPullback_kanComplex R C D M X Y
  have hs := dgGluingDerivedCompositionInputStrictPullback_kanComplex R C D M X Y
  dsimp only [dgGluingDerivedCompositionInputStrictPullback,
    dgGluingDerivedLastCompositionInputDiagonal, dgGluingDerivedFirstCompositionInputDiagonal] at hs
  letI := hs
  have hcoord := isFibrant_of_fibration
    (dgGluingCompositionInputStrictCoordinatesIso R C D M X Y).inv
  change KanComplex (Limits.pullback
    (dgGluingArrowCompositionEndpointPair (dgGluingDerivedAugmentationEdge R C D M X)
      (dgGluingDerivedAugmentationEdge R C D M Y))
    (MonoidalCategoryStruct.tensorHom (dgGluingDerivedLeftCoefficientInput R C D M X Y)
      (dgGluingDerivedRightCoefficientInput R C D M X Y))) at hcoord
  letI := hcoord
  have he : IsSimplicialHomotopyEquivalence
      (dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫
        (dgGluingLaxHomCoordinateTargetIso R C D M X Y).hom) :=
    (dgGluingHomotopyEquivalence_postcomp_iso_iff
      (dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y)
      (dgGluingLaxHomCoordinateTargetIso R C D M X Y)).mpr
        (dgGluingLaxHomIntervalCoordinatesTransport_equivalence R C D M X Y)
  apply he.cancel_right
  rw [dgGluingLaxHomCoordinateTargetIso_comparison]
  exact dgGluingLaxHomInputCoordinateComparison_equivalence R C D M X Y

def dgGluingLaxHomPullbackComparisonInverse :=
  (dgGluingLaxHomPullbackComparison_equivalence R C D M X Y).choose

def dgGluingLaxHomPullbackComparisonInverse_unit :
    SSet.Homotopy (dgGluingLaxHomPullbackComparison R C D M X Y ≫
      dgGluingLaxHomPullbackComparisonInverse R C D M X Y) (𝟙 _) :=
  (Classical.choose_spec (dgGluingLaxHomPullbackComparison_equivalence R C D M X Y)).1.some

def dgGluingLaxHomPullbackComparisonInverse_counit :
    SSet.Homotopy (dgGluingLaxHomPullbackComparisonInverse R C D M X Y ≫
      dgGluingLaxHomPullbackComparison R C D M X Y) (𝟙 _) :=
  (Classical.choose_spec (dgGluingLaxHomPullbackComparison_equivalence R C D M X Y)).2.some
end SerrePositivity.InfinityCategories
