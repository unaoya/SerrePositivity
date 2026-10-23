module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TwistedHomFunctorMap
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Core.VertexFiberPullback

/-!
概要：元の関手の twisted arrow 写像を、同じ元の両変数の底上の実比較にする。
方針：元の全射影の自然性で引き戻しへ持ち上げ、各元の twisted Hom 写像へ照合する。
規約：実際の全空間比較と各 fiber の同じ写像を保持する。
使われ方：充満忠実な元の関手の共同 Hom 図式の全自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の関手の twisted arrow 写像を、元の両変数の底に引き戻して比較する。 -/
def twistedArrowFunctorComparison {C D : SSet.{u}} (f : C ⟶ D) :
    TwistedArrow C ⟶ pullback (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f) :=
  pullback.lift (edgewiseSubdivisionMap f) (twistedArrowProjection C)
    (twistedArrowProjection_naturality f)

/-- 同じ元の全空間比較は、元の両変数の全射影を厳密に保持する。 -/
lemma twistedArrowFunctorComparison_projection {C D : SSet.{u}} (f : C ⟶ D) :
    twistedArrowFunctorComparison f ≫
      pullback.snd (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f) =
    twistedArrowProjection C := pullback.lift_snd _ _ _

/-- 元の全空間比較の各 fiber は、元の関手の同じ twisted Hom 写像そのもの。 -/
lemma twistedArrowFunctorComparison_fiber {C D : SSet.{u}} (f : C ⟶ D)
    (x y : C _⦋0⦌) :
    vertexFiberMap (twistedArrowProjection C)
        (pullback.snd (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f))
        (twistedArrowFunctorComparison f) (twistedArrowFunctorComparison_projection f)
        (SSet.opObjEquiv.symm x, y) ≫
      (vertexFiberPullbackIso (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f)
        (SSet.opObjEquiv.symm x, y)).hom = twistedHomFunctorMap f x y := by
  apply (cancel_mono (vertexFiberι (twistedArrowProjection D)
    ((SSet.opFunctor.map f ⊗ₘ f).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x, y)))).mp
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc, vertexFiberMap_ι,
    Category.assoc, twistedArrowFunctorComparison, pullback.lift_fst]
  rfl

/-- 充満忠実な元の関手の実際の twisted arrow 比較自身は、前合成同値。 -/
lemma twistedArrowFunctorComparison_isPrecompositionEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f) :
    IsPrecompositionEquivalence (twistedArrowFunctorComparison f) := by
  have : LeftFibration (pullback.snd (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f)) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection D))⟩
  apply isPrecompositionEquivalence_of_leftFibration_fibers (twistedArrowProjection C)
    (pullback.snd (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f))
    (twistedArrowFunctorComparison f) (twistedArrowFunctorComparison_projection f)
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective x
  have h := twistedHomFunctorMap_isQCatEquivalence f hf x y
  rw [← twistedArrowFunctorComparison_fiber] at h
  exact (qCatEquivalenceOfIso (vertexFiberPullbackIso (twistedArrowProjection D)
    (SSet.opFunctor.map f ⊗ₘ f) (SSet.opObjEquiv.symm x, y))).isQCatEquivalence.cancel_right h

end SerrePositivity.InfinityCategories.HomotopyLimits
