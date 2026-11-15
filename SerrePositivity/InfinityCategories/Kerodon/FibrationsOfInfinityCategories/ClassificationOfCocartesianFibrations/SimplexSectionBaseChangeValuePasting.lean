module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCompValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexNerveColimit
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionBaseChangeCompValueNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra

/-!
概要：全単体の指定底変換の合成則を同じ任意の係数に評価する。
方針：転置の頂点評価の既存の式と、元の実現の頂点表示を使う。
規約：図式全体の写像を比較する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の三因子の端点正規化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Project.QuasicategoryAuxiliaries
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：指定全単体底変換の合成則は、同じ左ファイブレーション係数での評価と両立。
方針：元の共同合成則を同じ評価で後合成し、後合成の合成則を使う。
規約：元の三因子と直接底変換を保持する。使われ方：分類底変換の中間同型の消去。
対応：Kerodon §5.6（Tag 027M）の既存分類構成の貼り合わせの法則。 -/
lemma simplexSectionBaseChange_value_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq (FunctorIso.postcomp (simplexSectionCompIso k l) evp ≪≫
        FunctorIso.postcomp (simplexSectionFirstIso k l) evp ≪≫
          FunctorIso.postcomp (simplexSectionSecondIso k l) evp)
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso (l ≫ k)) evp) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  have hg : U.map (nerveMap (transportSimplexFunctor (l ≫ k))) ≫
        transportSimplexSectionInfinity B =
      U.map (nerveMap (transportSimplexFunctor l)) ≫
        (U.map (nerveMap (transportSimplexFunctor k)) ≫
          transportSimplexSectionInfinity B) := by
    change (transportSimplexNerveFunctor ⋙ U).map (l ≫ k) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    rfl
  have h := functorIso_postcomp_heq_of_heq
    (transportSimplexSectionInfinity_baseChangeIso (l ≫ k))
    (simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l ≪≫ simplexSectionSecondIso k l)
    rfl hg (transportSimplexSectionInfinity_baseChange_pasting k l)
    (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))
  rw [functorIso_postcomp_trans, functorIso_postcomp_trans] at h
  exact h

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
