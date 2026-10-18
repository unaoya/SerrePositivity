module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramScaffoldAdjunction
public import SerrePositivity.InfinityCategories.F1.OppositeKanUnstraightening
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningLift
public import SerrePositivity.InfinityCategories.F1.WeightedNerveComparisonTransport
public import SerrePositivity.InfinityCategories.F1.LeftStrictTransportEquivalence
public import SerrePositivity.InfinityCategories.F1.KanDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningComparisonInvariance

/-!
概要：strict Kan 図式から反転した coherent 図式の小さい復元の strict transport への自然な比較。
方針：weighted nerve の比較を元の宇宙へ降ろし、scaffold の射の対応を逆向きに適用する。
規約：底は通常の圏の nerve、比較は全対象で同時に自然な変換として構成する。
使われ方：Kerodon Corollary 5.6.0.6、strict な図式の復元比較の単位と値の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の Kan 値の weighted nerve を反転した図式の小さい unstraightening へ写す。
方針：構成済みの大きい比較を縮小同型で元の宇宙へ降ろす。
規約：定義域・終域・底を同じ宇宙 u に揃える。
使われ方：Kerodon Corollary 5.6.0.6、scaffold の対応で図式全体の比較を作る入力。 -/
noncomputable def smallOppositeKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerve (F ⋙ kanObjectForget) ⟶
      smallLeftUnstraightening (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) :=
  smallLeftUnstraighteningLift (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))
    (oppositeKanUnstraighteningComparison F)

/-- 概要：小さい weighted nerve の比較は元の底を厳密に保つ。
方針：大きい比較の射影の式を小さい持ち上げの射影の判定へ適用する。
規約：底は持ち上げ前の nerve C。
使われ方：Kerodon Remark 5.6.2.5、小さい相対 Hom と scaffold へ入れる可換式。 -/
lemma smallOppositeKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    smallOppositeKanUnstraighteningComparison F ≫
      smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) =
      weightedNerveProjection (F ⋙ kanObjectForget) :=
  smallLeftUnstraighteningLift_projection _ _ _ (oppositeKanUnstraighteningComparison_projection F)

/-- 概要：反転した図式の小さい unstraightening への weighted nerve の比較は前合成同値。
方針：元の weighted nerve の left fibration 性を使い、大きい比較の同値性を小さい fiber へ降ろす。
規約：構成した底上の射そのものの同値性。
使われ方：Kerodon Corollary 5.6.0.6、構成する図式の比較の成分の同値性。 -/
lemma smallOppositeKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (smallOppositeKanUnstraighteningComparison F) := by
  have : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c ↦ (F.obj c).isKanComplex
  exact smallLeftUnstraighteningLift_isPrecompositionEquivalence _ _ _
    (oppositeKanUnstraighteningComparison_projection F)
    (oppositeKanUnstraighteningComparison_isPrecompositionEquivalence F)

/-- 概要：Kan 値 strict 図式を、反転した coherent 表示の小さい復元の strict transport へ写す自然変換。
方針：taut scaffold と小さい weighted 比較を合成した底上の射を、scaffold の全単射で転置する。
規約：対象ごとの比較の選択でなく、図式全体の一つの自然変換を得る。
使われ方：Kerodon Corollary 5.6.0.6、strict な図式と小さい復元の間の単位の比較。 -/
noncomputable def smallOppositeKanTransportUnit
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    F ⋙ kanObjectForget ⟶ leftStrictTransportDiagram
      (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))) :=
  (strictDiagramScaffoldHomEquiv (F ⋙ kanObjectForget)
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))).symm
    ⟨tautScaffold (F ⋙ kanObjectForget) ≫ smallOppositeKanUnstraighteningComparison F, by
      rw [Category.assoc, smallOppositeKanUnstraighteningComparison_projection,
        tautScaffold_projection]⟩

/-- 概要：weighted nerve の係数から標的 fiber への比較の包含は定値係数での全空間の比較。
方針：標準 fiber 同型と fiber の射の包含の計算を使う。
規約：係数図式や標的の充填性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、図式の単位の成分を既存の fiber 比較と同定する。 -/
lemma weightedNerveComparisonFiber_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F) (c : C) :
    weightedNerveComparisonFiber F q h hh c ≫ vertexFiberι q (nerveVertex c) =
      weightedNerveConstantLift F c ≫ h := by
  rw [weightedNerveComparisonFiber, Category.assoc, vertexFiberMap_ι, ← Category.assoc,
    weightedNerveFiberIso_hom_ι]

/-- 概要：小さい復元への図式の単位を恒等射で評価すると weighted nerve の係数の fiber 比較になる。
方針：scaffold の射の対応の評価式と taut scaffold の定値係数での式を使う。
規約：fiber への射そのものの等式。
使われ方：Kerodon Corollary 5.6.0.6、図式の単位の成分の同値性の判定。 -/
lemma smallOppositeKanTransportUnit_evaluate
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (smallOppositeKanTransportUnit F).app c ≫ leftStrictTransportEvaluate
      (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))) c =
    weightedNerveComparisonFiber (F ⋙ kanObjectForget)
      (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
      (smallOppositeKanUnstraighteningComparison F)
      (smallOppositeKanUnstraighteningComparison_projection F) c := by
  have he := strictDiagramScaffoldHomEquiv_symm_evaluate_ι (F ⋙ kanObjectForget)
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
    ⟨tautScaffold (F ⋙ kanObjectForget) ≫ smallOppositeKanUnstraighteningComparison F, by
      rw [Category.assoc, smallOppositeKanUnstraighteningComparison_projection,
        tautScaffold_projection]⟩ c
  apply vertexFiber_hom_ext _ (nerveVertex c)
  rw [weightedNerveComparisonFiber_ι]
  exact he.trans (by
    change simplicialReplacementConstantLift (F ⋙ kanObjectForget) c ≫
      (tautScaffold (F ⋙ kanObjectForget) ≫ smallOppositeKanUnstraighteningComparison F) = _
    rw [← Category.assoc, simplicialReplacementConstantLift_tautScaffold])

/-- 概要：strict Kan 図式から小さい復元の strict transport への単位の各成分は同値。
方針：恒等射評価の同値性と、weighted nerve の比較の fiber での同値性を二対三則で結ぶ。
規約：同値性は構成した一つの自然変換の全成分について述べる。
使われ方：Kerodon Corollary 5.6.0.6、strict な coherent 表示と復元後の straightening の比較。 -/
lemma smallOppositeKanTransportUnit_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    IsQCatEquivalence (X := (F.obj c).obj)
      (Y := leftStrictTransport
        (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))) c)
      ((smallOppositeKanTransportUnit F).app c) := by
  have : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c ↦ (F.obj c).isKanComplex
  apply (leftStrictTransportEvaluate_isQCatEquivalence
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))) c).cancel_right
  rw [smallOppositeKanTransportUnit_evaluate]
  exact weightedNerveComparisonFiber_isQCatEquivalence_of_precompositionEquivalence
    (F ⋙ kanObjectForget)
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
    (smallOppositeKanUnstraighteningComparison F)
    (smallOppositeKanUnstraighteningComparison_projection F)
    (smallOppositeKanUnstraighteningComparison_isPrecompositionEquivalence F) c

/-- 概要：strict Kan 図式の coherent 表示は、反転した表示の小さい復元の straightening と関手同型。
方針：構成した図式全体の自然変換を実現し、全成分の同値性で可逆な辺にする。
規約：同値の族だけでなく関手空間内の同型を与える。
使われ方：Kerodon Corollary 5.6.0.6、strict 表示の場合の coherent な単位の比較。 -/
noncomputable def smallOppositeKanStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningCandidate (smallLeftUnstraighteningProjection
        (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))) :=
  kanDiagramFunctorIsoOfPointwise (F := ⟨F, trivial⟩)
    (G := ⟨leftStrictTransportFunctor (smallLeftUnstraighteningProjection
      (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))), trivial⟩)
    (smallOppositeKanTransportUnit F) (smallOppositeKanTransportUnit_isQCatEquivalence F)

/-- 概要：strict Kan 図式の coherent 表示を小さく復元して straightening すると元の図式と関手同型。
方針：反転した表示での単位に係数の反転の関手同型による復元の不変性を合成する。
規約：任意の coherent 図式の strictification や写像空間の充満忠実性は含めない。
使われ方：Kerodon Corollary 5.6.0.6、strict な表現について図式全体の復元を確認する。 -/
noncomputable def strictKanStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningCandidate
        (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))) :=
  smallOppositeKanStraighteningUnitIso F ≪≫
    smallStraighteningCandidateIsoOfFunctorIso (kanDiagramOppositeComparisonIso F).symm

end SerrePositivity.InfinityCategories
