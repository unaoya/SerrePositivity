module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionComposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationRestrictionPullbackValue
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoChainTransport

/-!
概要：同じ全単体貼り合わせの二因子の係数を、引き戻し係数と前合成で読む。
方針：同じ端点移送、評価、前後合成の交換則を使う。
規約：元の指定比較を保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance simplexFactorValues_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma diagramIsoCongr_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g')
    (e : FunctorIso f g) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (diagramIsoCongr hf hg e) q) (FunctorIso.postcomp e q) :=
  functorIso_postcomp_heq_of_heq e (diagramIsoCongr hf hg e) hf hg
    (diagramIsoCongr_heq hf hg e) q

/-- 概要：第一段の因子の同じ係数値は、同じ引き戻し対象の第二段底変換。
方針：端点移送を消去し、同じ評価と後合成の結合則を使う。
規約：標準引き戻しを保持する。使われ方：中間制限同型の相殺。 -/
lemma simplexSectionFirstIso_value_heq {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (FunctorIso.postcomp (simplexSectionFirstIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (leftFibrationInfinityVertex (pullback.snd p k)))) := by
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have h₀ : HEq (FunctorIso.postcomp (simplexSectionFirstIso k l) evp)
      (FunctorIso.postcomp
        (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso l) P) evp) := by
    unfold simplexSectionFirstIso
    exact diagramIsoCongr_postcomp_heq _ _ _ _
  have h₁ := functorIso_postcomp_postcomp (transportSimplexSectionInfinity_baseChangeIso l) P evp
  have h₂ := functorIso_postcomp_heq_of_map_eq
    (transportSimplexSectionInfinity_baseChangeIso l) (leftFibrationBaseChange_evaluate p k)
  exact h₀.trans (h₁.heq.trans h₂.symm)

/-- 概要：第二段の因子の同じ係数値は、元の第一段底変換の添字前合成。
方針：前後合成の交換則を使う。規約：元の比較を保持する。
使われ方：二段底変換の同じ三因子の評価。 -/
lemma simplexSectionSecondIso_value {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso.postcomp (simplexSectionSecondIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)) =
      FunctorIso.precomp
        (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
          (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))) :=
  functorIso_precomp_postcomp (transportSimplexSectionInfinity_baseChangeIso k)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))) _

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
