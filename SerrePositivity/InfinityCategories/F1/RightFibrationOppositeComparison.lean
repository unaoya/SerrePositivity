module

public import SerrePositivity.InfinityCategories.F1.RightFibrationOppositeEnriched
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction

/-!
概要：元の相対 Hom の right fibration の ∞ 圏は、反対の底上の left fibration の ∞ 圏と同値。
方針：共通解像上の反転作用は全 Hom で同値で、対象は二重反転の底上の同型で復元する。
規約：coherent nerve の実際の射の充満忠実性と本質的全射性を合わせる。
使われ方：空間値 straightening を元の前層による right fibration の分類へ双対化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 反対の底上の left fibration を反転し、元の底への射影を持つ right fibration とする。 -/
def leftFibrationOppositeRightObject {B : SSet.{u}} (p : LeftFibrationObject B.op) :
    RightFibrationObject B :=
  ⟨Over.mk (SSet.opFunctor.map p.val.hom ≫ (SSet.opFunctorCompOpFunctorIso.app B).hom),
    ⟨rightFibrations.comp_mem _ _
      (RightFibration.mem (p := SSet.opFunctor.map p.val.hom))
      (MorphismProperty.of_isIso rightFibrations _)⟩⟩

/-- 二重反転の全空間の標準同型は、元の反対の底上の射影を厳密に保つ。 -/
lemma rightFibrationOppositeRoundTrip_projection {B : SSet.{u}}
    (p : LeftFibrationObject B.op) :
    (SSet.opFunctorCompOpFunctorIso.app p.val.left).hom ≫ p.val.hom =
      (rightFibrationOppositeObject (leftFibrationOppositeRightObject p)).val.hom := by
  convert (SSet.opFunctorCompOpFunctorIso.hom.naturality p.val.hom).symm using 1 <;> rfl

/-- 共通解像上の反転作用は、元の全相対 Hom で同値を誘導するので充満忠実。 -/
lemma rightFibrationOppositeEnriched_isFullyFaithful (B : SSet.{u}) :
    IsFullyFaithful (coherentNerveMap (rightFibrationOppositeEnriched B)) := by
  apply (coherentNerveMap_isFullyFaithful_iff _).mpr
  intro p q
  exact edgewiseRelativeFunctorOpposite_isQCatEquivalence q.val.val.hom p.val.val.hom

/-- 元の底が quasicategory なら、反対の底の任意の left fibration は元の right fibration の像と同型。 -/
lemma rightFibrationOppositeEnriched_isEssentiallySurjective
    (B : SSet.{u}) [Quasicategory B] :
    IsEssentiallySurjective (coherentNerveMap (rightFibrationOppositeEnriched B)) := by
  intro y
  let p := coherentNerveObject y
  let q := leftFibrationOppositeRightObject p
  refine ⟨coherentNerveVertex (⟨q, trivial⟩ : EdgewiseEnrichedObject (RightFibrationObject B)), ?_⟩
  rw [coherentNerveMap_vertex]
  have he := leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    (rightFibrationOppositeObject q).val.hom p.val.hom
    (SSet.opFunctorCompOpFunctorIso.app p.val.left).hom
    (rightFibrationOppositeRoundTrip_projection p)
    (isPrecompositionEquivalence_of_iso (SSet.opFunctorCompOpFunctorIso.app p.val.left))
  exact ⟨he ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk (coherentNerveVertex_object y))⟩

/-- 元の相対 Hom の共通解像から反対の底上の left fibrations への同じ比較射は同値。 -/
lemma rightFibrationOppositeEnriched_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    IsQCatEquivalence (coherentNerveMap (rightFibrationOppositeEnriched B)) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (rightFibrationOppositeEnriched_isFullyFaithful B)
    (rightFibrationOppositeEnriched_isEssentiallySurjective B)

/-- 元の right fibration の ∞ 圏から、反対の底上の left fibration の ∞ 圏への実際の比較。 -/
def rightFibrationOppositeInfinityMap (B : SSet.{u}) :
    RightFibrationInfinity B ⟶ LeftFibrationInfinity B.op :=
  (edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)).inv ≫
    coherentNerveMap (rightFibrationOppositeEnriched B)

/-- 元の right fibration の ∞ 圏の反転比較は同値。 -/
lemma rightFibrationOppositeInfinityMap_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    IsQCatEquivalence (rightFibrationOppositeInfinityMap B) :=
  (edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)).symm.isQCatEquivalence.comp
    (rightFibrationOppositeEnriched_isQCatEquivalence B)

/-- 実際の反転比較は、指定した元の right fibration の頂点を同じ反転射影の頂点へ写す。 -/
def rightFibrationOppositeInfinityVertexIso {B : SSet.{u}} (p : RightFibrationObject B) :
    VertexIso
      ((rightFibrationOppositeInfinityMap B).app _ (coherentNerveVertex p))
      (coherentNerveVertex (rightFibrationOppositeObject p)) := by
  have h := (FunctorIso.postcomp
    (edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)).homInvIso
    (coherentNerveMap (rightFibrationOppositeEnriched B))).app
    (coherentNerveVertex (⟨p, trivial⟩ : EdgewiseEnrichedObject (RightFibrationObject B)))
  change VertexIso
    ((rightFibrationOppositeInfinityMap B).app _
      ((coherentNerveMap (edgewiseEnrichedRight (RightFibrationObject B))).app _
        (coherentNerveVertex (⟨p, trivial⟩ : EdgewiseEnrichedObject (RightFibrationObject B)))))
    ((coherentNerveMap (rightFibrationOppositeEnriched B)).app _
      (coherentNerveVertex (⟨p, trivial⟩ : EdgewiseEnrichedObject (RightFibrationObject B)))) at h
  rw [coherentNerveMap_vertex, coherentNerveMap_vertex] at h
  exact h

end SerrePositivity.InfinityCategories
