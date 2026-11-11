module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorComparison

/-!
概要：全写像空間の内部 Hom から、cotensor 値への整合写像空間へ戻す射。
方針：各段評価に内部 Hom を施し、源交換の逆を合成して点つき普遍射へまとめる。
規約：射は全て実際の点つき射。使われ方：cotensor 交換同型の逆射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全写像空間の内部 Hom の各段評価を元の順序へ戻した族。 -/
def inverseExchangeFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    (ihom A).obj (pointedSpace X Y) ⟶
      PointedObject.basedHom (X.level n).space (PointedObject.basedHom A (Y.level n).space) :=
  (ihom A).map (pointedEvaluation X Y n) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).inv

/-- 逆交換した族は cotensor 値の構造条件を満たす。 -/
lemma inverseExchangeFamily_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    inverseExchangeFamily X Y A (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        (PointedObject.basedHom A (Y.level (n + 1)).space) =
      inverseExchangeFamily X Y A n ≫ pointedStep X (KanSequence.mapping A Y) n := by
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A (Y.level (n + 1)).space).hom).mp
  dsimp only [inverseExchangeFamily]
  rw [Category.assoc, Category.assoc, restriction_exchange, Iso.inv_hom_id_assoc,
    Category.assoc, Category.assoc, step_exchange, Iso.inv_hom_id_assoc,
    ← CategoryTheory.Functor.map_comp, pointedEvaluation_condition,
    CategoryTheory.Functor.map_comp]

/-- cotensor 値への写像空間に戻す実際の逆向きの射。 -/
def cotensorInverse (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) :
    (ihom A).obj (pointedSpace X Y) ⟶ pointedSpace X (KanSequence.mapping A Y) :=
  pointedLift X (KanSequence.mapping A Y) (inverseExchangeFamily X Y A)
    (fun n ↦ congrArg Under.Hom.right (inverseExchangeFamily_condition X Y A n))

@[reassoc]
lemma cotensorInverse_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    cotensorInverse X Y A ≫ pointedEvaluation X (KanSequence.mapping A Y) n =
      inverseExchangeFamily X Y A n := pointedLift_evaluation _ _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
