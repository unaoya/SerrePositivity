module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.TwistedHomFunctorMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback

/-!
概要：元の関手の twisted arrow 写像を、同じ元の両変数の底上の実比較にする。
方針：元の全射影の自然性で引き戻しへ持ち上げ、各元の twisted Hom 写像へ照合する。
規約：実際の全空間比較と各 fiber の同じ写像を保持する。
使われ方：充満忠実な元の関手の共同 Hom 図式の全自然同型。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 元の関手の twisted arrow 写像を、元の両変数の底に引き戻して比較する。 -/
def twistedArrowFunctorComparison {C D : SSet.{u}} (f : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_naturality f)

/-- 同じ元の全空間比較は、元の両変数の全射影を厳密に保持する。 -/
lemma twistedArrowFunctorComparison_projection {C D : SSet.{u}} (f : C ⟶ D) :
    twistedArrowFunctorComparison f ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C := pullback.lift_snd _ _ _

/-- 元の全空間比較の各 fiber は、元の関手の同じ twisted Hom 写像そのもの。 -/
lemma twistedArrowFunctorComparison_fiber {C D : SSet.{u}} (f : C ⟶ D)
    (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
        (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f))
        (twistedArrowFunctorComparison f) (twistedArrowFunctorComparison_projection f)
        (SSet.opObjEquiv.symm x, y) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f)
        (SSet.opObjEquiv.symm x, y)).hom = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedHomFunctorMap f x y := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D)
    ((SSet.opFunctor.map f ⊗ₘ f).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x, y)))).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
    Category.assoc, twistedArrowFunctorComparison, pullback.lift_fst]
  rfl

/-- 充満忠実な元の関手の実際の twisted arrow 比較自身は、前合成同値。 -/
lemma twistedArrowFunctorComparison_isPrecompositionEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (twistedArrowFunctorComparison f) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D))⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPrecompositionEquivalence_of_leftFibration_fibers (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f))
    (twistedArrowFunctorComparison f) (twistedArrowFunctorComparison_projection f)
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective x
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedHomFunctorMap_isQCatEquivalence f hf x y
  rw [← twistedArrowFunctorComparison_fiber] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D)
    (SSet.opFunctor.map f ⊗ₘ f) (SSet.opObjEquiv.symm x, y))).isQCatEquivalence.cancel_right h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
