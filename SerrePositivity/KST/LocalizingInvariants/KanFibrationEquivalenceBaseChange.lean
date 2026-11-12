module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativePathBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints

/-!
概要：Kan fibration に沿って同値を引き戻すと、元の比較射も同値になる。
方針：端点の RLP と Kan 性から可逆辺を持ち上げ、相対 path の全境界を充填する。
規約：モデル構造の右固有性は使わない。使われ方：Tamme の元の写像空間正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

lemma kanFibration_inner {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] : InnerFibration p := by
  have hp := (SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance
  exact ⟨fun _ _ i hi => hp i (innerHornInclusions_le_J i hi)⟩

lemma kanFibration_targetLifting {E B : SSet.{u}} [KanComplex E]
    (p : E ⟶ B) [Fibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting p := by
  intro x e _ ht
  have hp := (SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance
  have : HasLiftingProperty (stdSimplex.δ (0 : Fin 2)) p :=
    AnodyneHomotopy.delta_anodyne 0 1 (by decide) p hp
  have sq : CommSq (SSet.yonedaEquiv.symm x) (stdSimplex.δ (0 : Fin 2)) p e := ⟨by
    rw [ht, SSet.yonedaEquiv_symm_comp]⟩
  refine ⟨sq.lift, sq.fac_left, sq.fac_right, ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)

/-- 原型の四射のうち、fibration と交差する同値の引き戻し射そのものが同値。 -/
lemma kanPullback_first_equivalence {P E K B : SSet.{u}}
    [KanComplex P] [KanComplex E] [KanComplex K] [KanComplex B]
    {f : P ⟶ E} {g : P ⟶ K} {p : E ⟶ B} {e : K ⟶ B}
    (sq : IsPullback f g p e) [Fibration p] (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  have : InnerFibration p := kanFibration_inner p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration p
      (kanFibration_targetLifting p)
  have : InnerFibration (pullback.fst e p) :=
    ⟨innerFibrations.pullback_fst e p (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback e p) := quasicategory_of_innerFibration (pullback.fst e p)
  have h := he.isQCatEquivalence.pullback_snd_of_relativePath p
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso sq.flip.isoPullback).isQCatEquivalence.comp h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (sq.flip.isoPullback.hom ≫ pullback.snd e p) at hi
  rw [sq.flip.isoPullback_hom_snd] at hi
  exact hi.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
