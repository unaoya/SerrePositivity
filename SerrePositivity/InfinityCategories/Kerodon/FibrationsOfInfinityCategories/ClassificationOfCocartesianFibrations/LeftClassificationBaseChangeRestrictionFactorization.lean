module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationBaseChangeRestrictionValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeValue
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：指定分類底変換の制限を、同じ共同制限と切断比較の三因子へ分ける。
方針：元の指定同型の係数評価を取り、始域の等式移送だけを消去する。
規約：各因子に別の同型を選ばない。
使われ方：Kerodon §5.6（Tag 027M）の分類底変換の貼り合わせ則の中間因子の消去。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

private lemma eqIso_trans_postcomp_heq {A X Y : SSet.{u}}
    {F F' G : A ⟶ X} (h : F = F') (e : FunctorIso F' G) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (f := F) (g := G)
      (eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h) ≪≫ e) q)
      (FunctorIso.postcomp e q) := by
  cases h
  simpa only [eqToIso_refl, Iso.refl_trans] using (HEq.refl (FunctorIso.postcomp e q))

/-- 概要：指定分類底変換の元の対象成分は、同じ共同制限・切断比較・共同制限の三因子。
方針：元の共同比較の定義に係数評価を後合成し、始域の等式による移送を消去する。
規約：同じ三因子全体の異種等式。使われ方：二段の底変換の中間同型の消去。 -/
lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_factors
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        (U.map (transportSimplexFirstVertexMap D)))
      (FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t) evp ≪≫
        FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp ≪≫
          FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
            evp) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  let e₃ := (leftStraighteningSectionJointDiagram_restrictIso B).precomp t ≪≫
    (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
      ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
  have hp := (leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_heq p k).trans
    (functorIsoValue_transpose_heq_postcomp (straighteningBaseChangeRestrictionIso k)
      (leftFibrationInfinityVertex p))
  have hr : HEq (FunctorIso.postcomp (straighteningBaseChangeRestrictionIso k) evp)
      (FunctorIso.postcomp e₃ evp) := by
    change HEq (FunctorIso.postcomp (eqToIso
      (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
        (straighteningBaseChange_firstVertex_source k)) ≪≫ e₃) evp) (FunctorIso.postcomp e₃ evp)
    exact eqIso_trans_postcomp_heq (straighteningBaseChange_firstVertex_source k) e₃ evp
  have h₃ : FunctorIso.postcomp e₃ evp =
      FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t) evp ≪≫
        FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp ≪≫
          FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
            evp := by
    dsimp only [e₃]
    rw [Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
      Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  exact hp.trans (hr.trans h₃.heq)

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
