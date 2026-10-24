module
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.Fibration.TransportSectionBaseChangePoint
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 同じ straightening 底変換同型を全単体へ戻すと、元の指定比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 元の大域底変換の定義で選んだ、同じ全単体上の制限比較を明示する。 -/
def straighteningJointBaseChangeRestrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        (leftStraighteningSectionJointDiagram D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hleft) ≪≫
    (leftStraighteningSectionJointDiagram_restrictIso B).precomp t ≪≫
    (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
    ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm

/-- Sp の前合成充満忠実性を使い、元の大域同型の制限が同じ指定比較であると回収する。 -/
theorem leftStraighteningSectionJointDiagram_baseChangeIso_pre [Quasicategory D] :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap D))).app
        ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u}))).toFunctor.map
          (leftStraighteningSectionJointDiagram_baseChangeIso k).hom =
      (straighteningJointBaseChangeRestrictionIso k).hom := by
  exact (localizationPre_fullyFaithful
    (Y := (ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u}) _ _
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} D)
    ).toHoFullyFaithful.map_preimage _

/-- 初頂点の同じ値で、元の大域成分を元の全単体上の指定成分として回収する。 -/
theorem leftStraighteningSectionJointDiagram_baseChangeIso_value [Quasicategory D]
    (c : TransportSimplexCategory D) :
    functorHomEvaluate (leftStraighteningSectionJointDiagram_baseChangeIso k).hom
      (ULift.up ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
    functorHomEvaluate (straighteningJointBaseChangeRestrictionIso k).hom
      (ULift.up (nerveVertex c)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)
  let a := ULift.up.{u + 1} (nerveVertex c)
  let F := (SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B
  let G := leftStraighteningSectionJointDiagram D ≫
    (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have h := congrArg (fun m : FunctorHom (l ≫ F) (l ≫ G) => functorHomEvaluate m a)
    (leftStraighteningSectionJointDiagram_baseChangeIso_pre k)
  have hp := functorHomEvaluate_precomp
    (leftStraighteningSectionJointDiagram_baseChangeIso k).hom l a
  exact hp.symm.trans h

end SerrePositivity.KST.Fibration
