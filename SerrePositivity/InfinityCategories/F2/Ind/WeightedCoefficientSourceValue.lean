module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedSourceElementsEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedIdentityFiberEquivalence

/-!
概要：共同分類の同じ係数復元を、元の始点固定 twisted-arrow 評価と合成する。
方針：元の反転 fiber を同じ反対底の fiber へ移し、復元の実際の fiber 写像で写す。
規約：指定復元を保持。使われ方：native 係数余錐の評価比較の恒等 fiber 側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
local notation "R" => weightedLeftCoefficientRecovery (F ⋙ rightFibrationOppositeOrdinary C) i

/-- 同じ元の始点固定評価を、同じ係数復元の指定値へ写す。 -/
def weightedCoefficientCanonicalSourceValue : twistedSourceElements (F.obj i).val.hom x ⟶
    vertexFiber (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x) :=
  twistedSourceElementsEvaluation (F.obj i).val.hom x ≫
    (vertexFiberOpIso (F.obj i).val.hom x).hom ≫
      vertexFiberMap (SSet.opFunctor.map (F.obj i).val.hom)
        (smallLeftUnstraighteningProjection Q) R
        (weightedLeftCoefficientRecovery_projection (F ⋙ rightFibrationOppositeOrdinary C) i)
        (SSet.opObjEquiv.symm x)

/-- 指定値の全空間へ含めると、元の始点固定持ち上げと同じ復元の合成。 -/
lemma weightedCoefficientCanonicalSourceValue_ι :
    weightedCoefficientCanonicalSourceValue F i x ≫
      vertexFiberι (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x) =
        twistedSourceElementsComparison (F.obj i).val.hom x ≫
          twistedArrowSourceLift (F.obj i).val.hom ≫ R := by
  rw [weightedCoefficientCanonicalSourceValue, Category.assoc, Category.assoc, vertexFiberMap_ι]
  have h : (vertexFiberOpIso (F.obj i).val.hom x).hom ≫
      vertexFiberι (SSet.opFunctor.map (F.obj i).val.hom) (SSet.opObjEquiv.symm x) =
        SSet.opFunctor.map (vertexFiberι (F.obj i).val.hom x) := rfl
  rw [← Category.assoc (vertexFiberOpIso (F.obj i).val.hom x).hom,
    h, ← Category.assoc, twistedSourceElementsEvaluation_ι]
  rfl

/-- 同じ恒等点上の作用は、元の評価同値と元の復元 fiber 同値の合成そのもの。 -/
lemma weightedCoefficientCanonicalSourceValue_identity_isQCatEquivalence :
    IsQCatEquivalence (twistedSourceElementsIdentityInclusion (F.obj i).val.hom x ≫
      weightedCoefficientCanonicalSourceValue F i x) := by
  rw [weightedCoefficientCanonicalSourceValue, ← Category.assoc,
    twistedSourceElementsEvaluation_identity]
  have : KanComplex (vertexFiber (F.obj i).val.hom x) := vertexFiber_kanComplex _ _
  exact (twistedIdentityFiberEvaluation_isQCatEquivalence (F.obj i).val.hom x).comp
    ((qCatEquivalenceOfIso (vertexFiberOpIso (F.obj i).val.hom x)).isQCatEquivalence.comp
      (weightedLeftCoefficientRecovery_fiber_isQCatEquivalence
        (F ⋙ rightFibrationOppositeOrdinary C) i (SSet.opObjEquiv.symm x)))

end SerrePositivity.InfinityCategories.F2.Ind
