module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingExchange

/-!
概要：cotensor 値への整合写像空間から、全写像空間の内部 Hom への実際の比較。
方針：各段で源を交換し、uncurry した族を点つき普遍射へまとめて curry する。
規約：標的の Kan 列は任意。使われ方：loop と写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 内部 Hom の源を交換した各段評価。 -/
def exchangeFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    pointedSpace X (KanSequence.mapping A Y) ⟶
      (ihom A).obj (PointedObject.basedHom (X.level n).space (Y.level n).space) :=
  pointedEvaluation X (KanSequence.mapping A Y) n ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom

/-- 交換した各段評価も元の構造条件を保つ。 -/
lemma exchangeFamily_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    exchangeFamily X Y A (n + 1) ≫
        (ihom A).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space) =
      exchangeFamily X Y A n ≫ (ihom A).map (pointedStep X Y n) := by
  dsimp only [exchangeFamily]
  rw [Category.assoc, ← restriction_exchange, ← Category.assoc]
  erw [pointedEvaluation_condition X (KanSequence.mapping A Y) n]
  rw [Category.assoc, step_exchange, ← Category.assoc]

/-- 交換した族を uncurry した点つき族の構造可換性。 -/
lemma uncurryExchangeFamily_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    uncurry (exchangeFamily X Y A (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
      uncurry (exchangeFamily X Y A n) ≫ pointedStep X Y n := by
  rw [← uncurry_natural_right, ← uncurry_natural_right, exchangeFamily_condition]

/-- 各段の交換した族を全写像空間へまとめた実際の射。 -/
def cotensorComparisonUncurried (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) :
    A ⊗ pointedSpace X (KanSequence.mapping A Y) ⟶ pointedSpace X Y :=
  pointedLift X Y (fun n ↦ uncurry (exchangeFamily X Y A n))
    (fun n ↦ congrArg Under.Hom.right (uncurryExchangeFamily_condition X Y A n))

/-- cotensor 値への写像から、元の全写像空間の内部 Hom への比較。 -/
def cotensorComparison (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) :
    pointedSpace X (KanSequence.mapping A Y) ⟶ (ihom A).obj (pointedSpace X Y) :=
  curry (cotensorComparisonUncurried X Y A)

@[reassoc]
lemma cotensorComparison_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    cotensorComparison X Y A ≫ (ihom A).map (pointedEvaluation X Y n) =
      exchangeFamily X Y A n := by
  apply uncurry_injective
  rw [uncurry_natural_right, cotensorComparison, uncurry_curry]
  exact pointedLift_evaluation _ _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
