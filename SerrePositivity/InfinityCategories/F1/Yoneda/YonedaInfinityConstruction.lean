module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.LeftFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.UniversalCoherentReconstructionComponents
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：twisted arrow の実際の分類図式から、空間値 Hom 関手と Yoneda 写像を構成する。
方針：両端射影を straighten し、宇宙持ち上げと直積の同型を経て第二変数で curry する。
規約：構成した一つの写像を固定する。表現可能な right fibration との照合と充満忠実性は別工程。
使われ方：F1-2 の全対象・全高次の Yoneda 関手と、その実際の写像空間作用の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- twisted arrow の両端射影の実際の分類図式としての空間値 Hom 関手。 -/
def twistedArrowHomInfinity (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ C) ⟶ SpaceInfinity.{u} :=
  leftStraighteningInfinityDiagram (twistedArrowProjection C)

/-- 二つの変数の宇宙持ち上げを分けた、同じ Hom 関手の共同評価。 -/
def homInfinityJointEvaluation (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u} :=
  (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op C).inv ≫ twistedArrowHomInfinity C

/-- 実際の共同 Hom 関手を curry した、前層 ∞ 圏への Yoneda 写像。 -/
def yonedaInfinityMap (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity C :=
  curry (homInfinityJointEvaluation C)

/-- Yoneda 写像の実際の共同評価は、元の twisted arrow の分類図式からの評価そのもの。 -/
lemma yonedaInfinityMap_uncurry (C : SSet.{u}) [Quasicategory C] :
    uncurry (yonedaInfinityMap C) = homInfinityJointEvaluation C :=
  uncurry_curry _

/-- 指定対象に第二変数を固定した、実際の空間値表現可能前層の図式。 -/
def representablePresheafInfinity {C : SSet.{u}} [Quasicategory C] (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u} :=
  lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C.op))
    (SSet.const (ULift.up c)) ≫ homInfinityJointEvaluation C

/-- Yoneda 写像の頂点は、同じ共同評価を制限した表現可能前層の図式の頂点。 -/
lemma yonedaInfinityMap_vertex {C : SSet.{u}} [Quasicategory C] (c : C _⦋0⦌) :
    (yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up c) =
      functorVertex (representablePresheafInfinity c) := by
  have h := (functorVertex_uncurry_at_vertex (yonedaInfinityMap C) (ULift.up c)).symm
  rw [yonedaInfinityMap_uncurry] at h
  exact h

end SerrePositivity.InfinityCategories
