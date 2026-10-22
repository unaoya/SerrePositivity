module
public import SerrePositivity.KST.Fibration.RelativePullbackRowPair
public import SerrePositivity.KST.SConstruction.RelativeIteratedRows

/-! # 相対引き戻しの元の二評価の全反復行と対角比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 最内側の全 S_n 行で、元の射影と quotient を束ねる自然な射対。 -/
def RelativePullback.iteratedPairDiagram {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (r : ℕ) :
    iteratedSRealizationDiagram r D.total ⟶
      iteratedSRealizationDiagram r D.base ⊗
        iteratedSRealizationDiagram r (closedStableModel B) :=
  lift (iteratedSRealizationDiagramMap r D.projection)
    (iteratedSRealizationDiagramMap r (D.cofiber ≫ relativeCofiberQuotient A B))

/-- 最内側の行全体を対角実現した、同じ元の二評価の射対。 -/
def RelativePullback.iteratedPair {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (r : ℕ) :
    iteratedSRealization r D.total ⟶ iteratedSRealization r D.base ⊗
      iteratedSRealization r (closedStableModel B) :=
  simplicialDiagonalFunctor.map (D.iteratedPairDiagram r) ≫
    (diagonalTensorIso (iteratedSRealizationDiagram r D.base)
      (iteratedSRealizationDiagram r (closedStableModel B))).hom

/-- 対角実現後も元の射影と quotient の順序付きの射対を厳密に回収する。 -/
lemma RelativePullback.iteratedPair_eq {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (r : ℕ) :
    D.iteratedPair r = lift (iteratedSRealizationMap r D.projection)
      (iteratedSRealizationMap r (D.cofiber ≫ relativeCofiberQuotient A B)) :=
  diagonalTensorIso_pair _ _

/-- 前段の全相対引き戻し比較から、元の同じ射対の次の反復対角での同値性を得る。 -/
lemma RelativePullback.iteratedPair_localized_isIso (r : ℕ)
    (hr : ∀ (Y : StableModel.{u}) (P Q : ClosedStablePredicate Y) (E : RelativePullback Y P Q),
      IsIso (AnodyneHomotopy.anodyneQ.map (E.pair (multiRealizationFunctor r))))
    {X : StableModel.{u}} {A B : ClosedStablePredicate X} (D : RelativePullback X A B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.iteratedPair r)) := by
  have hrows (n : SimplexCategoryᵒᵖ) :
      IsIso (AnodyneHomotopy.anodyneQ.map ((D.iteratedPairDiagram r).app n)) :=
    D.rowPair_localized_isIso n.unop.len (multiRealizationFunctor r)
      (hr _ _ _ (D.sRow n.unop.len))
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (D.iteratedPairDiagram r))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map (D.iteratedPairDiagram r) hrows
  rw [RelativePullback.iteratedPair, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
