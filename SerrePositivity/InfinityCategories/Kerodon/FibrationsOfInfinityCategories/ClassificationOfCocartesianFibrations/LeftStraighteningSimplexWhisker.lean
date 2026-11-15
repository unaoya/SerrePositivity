module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexPastingInputs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：二段底変換の第一の指定同型の制限を、同じ全単体制限と係数で計算する。
方針：初頂点の自然性と同じ同型の前合成・端点正規化の法則を使う。
規約：元の指定同型を保持する。
使われ方：Kerodon §5.6（Tag 027M）の中間制限同型の相殺。
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
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance simplexWhisker_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：第一の底変換を第二の底の初頂点で制限した同型は同じ前合成した共役。
方針：前合成の合成則と初頂点の自然性を、同じ正規化した共役表示へ適用する。
規約：全図式の同じ同型の等式。使われ方：二段の底変換の中間同型を相殺する。 -/
lemma leftStraightening_baseChange_simplex_whisker
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
        Category.assoc])
      (((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map l)).precomp
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        ((simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        ((leftClassificationSimplexIso (pullback.snd p k)).precomp t).symm := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor l))
  let s := U.map (nerveMap (transportSimplexFunctor k))
  let fD := U.map (transportSimplexFirstVertexMap D)
  let fT := U.map (transportSimplexFirstVertexMap T)
  let b := leftStraighteningInfinityDiagram_baseChangeIso p k
  have hs : fD ≫ (U.map k ≫ leftStraighteningInfinityDiagram p) =
      s ≫ (U.map (transportSimplexFirstVertexMap B) ≫ leftStraighteningInfinityDiagram p) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  let N := diagramIsoCongr hs rfl (b.precomp fD)
  have h₀ := functorIso_precomp_precomp b (U.map l) fT
  have h₁ := functorIso_precomp_heq_of_map_eq b
    (transportSimplexFirstVertexMap_ulift_naturality l).symm
  have h₂ := functorIso_precomp_precomp b fD t
  have hr : HEq ((b.precomp (U.map l)).precomp fT) ((b.precomp fD).precomp t) :=
    h₀.heq.trans (h₁.trans h₂.symm.heq)
  have hn := functorIso_precomp_heq_of_heq (b.precomp fD) N hs rfl
    (diagramIsoCongr_heq hs rfl (b.precomp fD)) t
  have hv := congrArg (fun e : FunctorIso
      (s ≫ (U.map (transportSimplexFirstVertexMap B) ≫ leftStraighteningInfinityDiagram p))
      (fD ≫ leftStraighteningInfinityDiagram (pullback.snd p k)) ↦
        FunctorIso.precomp e t) (leftStraightening_baseChange_simplex_normalized p k)
  simp only [functorIso_precomp_trans, functorIso_precomp_symm] at hv
  exact eq_of_heq ((diagramIsoCongr_heq _ _ _).trans
    (hr.trans (hn.symm.trans hv.heq)))

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
