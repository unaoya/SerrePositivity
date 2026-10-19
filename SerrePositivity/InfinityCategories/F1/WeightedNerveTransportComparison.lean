module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveTransportUnit
public import SerrePositivity.InfinityCategories.F1.KanEnrichedComparisonIso
public import SerrePositivity.InfinityCategories.F1.StrictTransportImageEvaluation
public import SerrePositivity.InfinityCategories.F1.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningCandidate

/-!
概要：weighted nerve の標準単位を全図式の coherent な族の比較へ実現する。
方針：底の対象で評価した単位の豊穣自然性を束ね、成分の同値性を関手同型へ移す。
規約：図式の変換空間の Kan 性や境界を固定した strictification は仮定しない。
使われ方：Kerodon Corollary 5.6.0.6、§5.6.5 の相対比較に向けた標準単位。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：底の対象で評価した標準単位は全ての高次変換に関して自然。
方針：変換空間の前後合成の可換式を成分で評価する。
規約：始域は全 strict Kan 図式の単体的圏。
使われ方：Kerodon Corollary 5.6.0.6、coherent な比較の実現の入力。 -/
noncomputable def weightedNerveTransportKanComparison
    {C : Type u} [Category.{u} C] (c : C) :
    KanEnrichedComparison (kanDiagramEvaluationEnriched c)
      (((weightedNerveKanEnriched C).comp SSet leftStrictTransportEnriched).comp SSet
        (strictTransportDiagramEvaluationEnriched c)) := by
  refine ⟨(fun F ↦ (weightedNerveTransportUnit (F.val ⋙ kanObjectForget)).app c), ?_⟩
  intro F G
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, η⟩
  have h := congrArg (fun f ↦
    (((f.app n η).val c).app n (𝟙 n) x))
    (weightedNerveTransportUnit_enrichedNaturality
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget))
  exact h.symm

/-- 概要：coherent な比較の各図式での辺は標準単位の成分そのもの。
方針：豊穣比較の実現の頂点評価公式を使う。
規約：ホモトピー類の一致に弱めない。
使われ方：Kerodon §5.6.5、固定した比較との照合。 -/
lemma weightedNerveTransportKanComparison_edge_at
    {C : Type u} [Category.{u} C] (c : C) (F : KanDiagramObject C) :
    (functorEdgeAt (kanEnrichedComparisonEdge (weightedNerveTransportKanComparison c))
      (coherentNerveVertex F)).edge =
      (coherentNerveEdge (show (kanDiagramEvaluationEnriched c).obj F ⟶
        ((((weightedNerveKanEnriched C).comp SSet leftStrictTransportEnriched).comp SSet
          (strictTransportDiagramEvaluationEnriched c)).obj F) from
        (weightedNerveTransportUnit (F.val ⋙ kanObjectForget)).app c)).edge :=
  kanEnrichedComparisonEdge_at (weightedNerveTransportKanComparison c) F

/-- 概要：weighted nerve 後の strict transport は全図式の coherent な評価と関手同型。
方針：豊穣比較を実現し、標準単位の各成分の同値性を使う。
規約：底の対象 c を固定し、図式の coherent パラメーターは全次数を保つ。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な族に引き戻せる評価の比較。 -/
noncomputable def weightedNerveTransportEvaluationIso
    {C : Type u} [Category.{u} C] (c : C) :
    FunctorIso (kanDiagramNerveEvaluation c)
      (weightedNerveInfinityMap C ≫ leftStrictTransportInfinityMap C ≫
        strictTransportDiagramInfinityEvaluation c) := by
  have h := kanEnrichedComparisonIso (weightedNerveTransportKanComparison c)
    (fun F ↦ by
      have : ∀ d, KanComplex ((F.val ⋙ kanObjectForget).obj d) :=
        fun d ↦ (F.val.obj d).isKanComplex
      exact weightedNerveTransportUnit_isQCatEquivalence (F.val ⋙ kanObjectForget) c)
  simpa only [coherentNerveMap_comp, Category.assoc,
    weightedNerveInfinityMap, leftStrictTransportInfinityMap,
    strictTransportDiagramInfinityEvaluation, kanDiagramNerveEvaluation] using h

/-- 概要：coherent な weighted nerve の復元比較を既存の straightening の評価へ接続する。
方針：strict transport の像の評価と straightening の評価の厳密な一致を使う。
規約：対象ごとの同型から底全体の関手同型を推論するものではない。
使われ方：Kerodon §5.6.5、相対比較の評価における整合性。 -/
noncomputable def weightedNerveStraighteningEvaluationIso
    {C : Type u} [Category.{u} C] (c : C) :
    FunctorIso (kanDiagramNerveEvaluation c)
      (weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C ≫
        evaluateFunctorAt (ULift.up (nerveVertex c))) := by
  rw [← leftStrictTransportInfinityMap_evaluate_straightening]
  exact weightedNerveTransportEvaluationIso c

/-- 概要：任意の coherent な strict 図式の族へ標準単位の評価比較を引き戻す。
方針：構成済みの大域的な関手同型を族 A で前合成する。
規約：パラメーター空間 B の quasicategory 性は不要。
使われ方：Kerodon §5.6.5、単体とその境界上の既存の族に対する比較。 -/
noncomputable def weightedNerveStraighteningFamilyEvaluationIso
    {C : Type u} [Category.{u} C] {B : SSet.{u + 1}}
    (A : B ⟶ KanDiagramNerve C) (c : C) :
    FunctorIso (A ≫ kanDiagramNerveEvaluation c)
      (A ≫ weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C ≫
        evaluateFunctorAt (ULift.up (nerveVertex c))) :=
  (weightedNerveStraighteningEvaluationIso c).precomp A

/-- 概要：一つの strict Kan 図式の標準単位を底全体の coherent な関手同型にする。
方針：図式全体の自然変換を実現し、各成分の同値性を適用する。
規約：図式 F は固定する。F の族に関する大域的な関手同型は別途構成する。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve による strict な復元の単位。 -/
noncomputable def weightedNerveStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningCandidate ((weightedNerveKanEnriched C).obj ⟨F, trivial⟩).val.hom) := by
  have : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) :=
    fun c ↦ (F.obj c).isKanComplex
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨F, trivial⟩)
    (G := ⟨leftStrictTransportFunctor (weightedNerveProjection (F ⋙ kanObjectForget)), trivial⟩)
    (weightedNerveTransportUnit (F ⋙ kanObjectForget))
    (weightedNerveTransportUnit_isQCatEquivalence (F ⋙ kanObjectForget))

end SerrePositivity.InfinityCategories
