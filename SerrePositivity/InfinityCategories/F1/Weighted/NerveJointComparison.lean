module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveDiagonalComparison
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramRealizationComparison

/-!
概要：weighted nerve の標準単位を底と図式の族の共同評価へ実現する。
方針：対角比較の二点図式を各単体で組み立て、面・退化と可換な族にする。
規約：値ごとの同型を選び直さず、一つの単体集合の射を構成する。
使われ方：Kerodon §5.6.5、straightening の大域的な単位の共同実現。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底と図式の族の各単体を、単位の二点図式の coherent な単体へ写す。
方針：対角比較の同時添字変換則を単体的自然性に用いる。
規約：始域は持ち上げた底と全 strict Kan 図式の coherent nerve の直積。
使われ方：Kerodon Corollary 5.6.0.6、単位の共同実現の入力。 -/
noncomputable def weightedNerveJointArrow (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ KanDiagramNerve C ⟶
      KanDiagramNerve (ULift.{u} (Fin 2)) where
  app _ := ↾fun s ↦ weightedNerveDiagonalArrow (kanDiagramSimplexBase s.1.down) s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, F⟩
    exact (weightedNerveDiagonalArrow_reindex α.unop.toOrderHom.uliftMap
      (kanDiagramSimplexBase σ.down) F).symm

/-- 概要：単位の共同評価を二点の底に値を取る coherent な族へ実現する。
方針：二点図式の coherent nerve に構成済みの共同実現を適用する。
規約：この一つの族で底と図式の両方を同時に動かす。
使われ方：Kerodon §5.6.5、転置による実際の比較の辺。 -/
noncomputable def weightedNerveJointComparisonFamily (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ KanDiagramNerve C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 2)))) :=
  weightedNerveJointArrow C ≫ kanDiagramRealization _

/-- 概要：単位の共同族の零側は元の Kan 図式の共同評価。
方針：二点図式の零成分が対角評価であることを全単体で使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon §5.6.5、共同比較の始点。 -/
lemma weightedNerveJointComparisonFamily_zero (C : Type u) [Category.{u} C] :
    weightedNerveJointComparisonFamily C ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) =
        kanDiagramJointEvaluation C := by
  rw [weightedNerveJointComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, F⟩
  change (weightedNerveDiagonalArrow (kanDiagramSimplexBase σ.down) F).comp SSet
    (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = _
  exact kanEnrichedComparisonArrowEnriched_zero
    (weightedNerveDiagonalKanComparison (kanDiagramSimplexBase σ.down) F)

/-- 概要：単位の共同族の一側は weighted nerve 後の図式の共同評価。
方針：二点図式の一成分が復元した対角評価であることを使う。
規約：coherent nerve の全次数で成立する等式。
使われ方：Kerodon §5.6.5、共同比較の終点。 -/
lemma weightedNerveJointComparisonFamily_one (C : Type u) [Category.{u} C] :
    weightedNerveJointComparisonFamily C ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) =
        (𝟙 _ ⊗ₘ coherentNerveMap (weightedNerveTransportDiagramEnriched C)) ≫
          kanDiagramJointEvaluation C := by
  rw [weightedNerveJointComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, F⟩
  change (weightedNerveDiagonalArrow (kanDiagramSimplexBase σ.down) F).comp SSet
    (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = _
  exact kanEnrichedComparisonArrowEnriched_one
    (weightedNerveDiagonalKanComparison (kanDiagramSimplexBase σ.down) F)

/-- 概要：単位の共同族を転置し、二つの共同評価の間の実際の辺を得る。
方針：二点の底の標準辺を転置した族で写す。
規約：始点・終点を共同族の厳密な評価式で同定する。
使われ方：Kerodon Corollary 5.6.0.6、大域的な単位の共同評価。 -/
noncomputable def weightedNerveJointComparisonEdge (C : Type u) [Category.{u} C] :
    Edge (functorVertex (kanDiagramJointEvaluation C))
      (functorVertex ((𝟙 _ ⊗ₘ coherentNerveMap (weightedNerveTransportDiagramEnriched C)) ≫
        kanDiagramJointEvaluation C)) :=
  (coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (weightedNerveJointComparisonFamily C))).ofEq
      (by rw [transposeFunctorFamily_vertex, weightedNerveJointComparisonFamily_zero])
      (by rw [transposeFunctorFamily_vertex, weightedNerveJointComparisonFamily_one])

/-- 概要：共同比較を底の対象と図式の組で評価すると標準単位の成分の辺になる。
方針：転置の評価を底の定値図式に戻し、一対象評価の二点図式を使う。
規約：一単体そのものの厳密な等式。
使われ方：Kerodon §5.6.5、共同比較の点ごとの可逆性。 -/
lemma weightedNerveJointComparisonEdge_at
    {C : Type u} [Category.{u} C] (c : C) (F : KanDiagramObject C) :
    (functorEdgeAt (weightedNerveJointComparisonEdge C)
      (ULift.up (nerveVertex c), coherentNerveVertex F)).edge =
      (coherentNerveEdge ((weightedNerveTransportKanComparison c).val F)).edge := by
  change ((coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (weightedNerveJointComparisonFamily C))).map
      (evaluateFunctorAt (ULift.up (nerveVertex c), coherentNerveVertex F))).edge = _
  rw [transposeFunctorFamily_edgeAt]
  let s := PinchedHom.constant
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ KanDiagramNerve C)
    (ULift.up (nerveVertex c), coherentNerveVertex F) 1
  change kanDiagramDiagonalSimplex coherentResolutionComparisonIndexEdge.edge.down
    ((KanDiagramNerve (ULift.{u} (Fin 2))).map (𝟙 (Opposite.op ⦋1⦌))
      (weightedNerveDiagonalArrow (kanDiagramSimplexBase s.1.down) s.2)) = _
  rw [Functor.map_id_apply]
  have hbase : kanDiagramSimplexBase s.1.down =
      (Functor.const (ULift.{u} (Fin 2))).obj c := rfl
  have hF : s.2 = PinchedHom.constant (coherentNerveVertex F) 1 := rfl
  rw [hbase, hF]
  rw [weightedNerveDiagonalArrow_constant]
  change kanDiagramDiagonalSimplex coherentResolutionComparisonIndexEdge.edge.down
    ((coherentNerveMap
      (kanEnrichedComparisonArrowEnriched (weightedNerveTransportKanComparison c))).app
      (Opposite.op ⦋1⦌) (PinchedHom.constant (coherentNerveVertex F) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex, kanDiagramDiagonalSimplex_constant]
  exact kanDiagramCoherentNerve_edge
    (kanEnrichedComparisonDiagram (weightedNerveTransportKanComparison c) F) _

/-- 概要：単位の共同比較は関手空間内の可逆な辺。
方針：底の頂点と図式を復元し、標準単位の成分の同値性で判定する。
規約：始域の共同パラメーター空間の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、大域的な単位を関手同型へ束ねる。 -/
lemma weightedNerveJointComparisonEdge_isInvertible
    (C : Type u) [Category.{u} C] :
    IsInvertibleEdge (weightedNerveJointComparisonEdge C) := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt
    (weightedNerveJointComparisonEdge C).toTruncated).mpr
  rintro ⟨⟨s⟩, t⟩
  obtain ⟨c, rfl⟩ : ∃ c : C, s = nerveVertex c :=
    ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  rw [← coherentNerveVertex_object t]
  apply (isInvertibleEdge_congr (weightedNerveJointComparisonEdge_at c (coherentNerveObject t))).mpr
  apply coherentKanEdge_isInvertible_of_isQCatEquivalence
  have : ∀ d, KanComplex (((coherentNerveObject t).val ⋙ kanObjectForget).obj d) :=
    fun d ↦ ((coherentNerveObject t).val.obj d).isKanComplex
  exact weightedNerveTransportUnit_isQCatEquivalence _ c

/-- 概要：元の共同評価と weighted nerve 後の共同評価は関手同型。
方針：構成した可逆な比較の辺の類を同型として束縛する。
規約：比較の順方向は実際に構成した共同比較の辺。
使われ方：Kerodon Corollary 5.6.0.6、二変数で coherent な復元単位。 -/
noncomputable def weightedNerveJointComparisonIso (C : Type u) [Category.{u} C] :
    FunctorIso (kanDiagramJointEvaluation C)
      ((𝟙 _ ⊗ₘ coherentNerveMap (weightedNerveTransportDiagramEnriched C)) ≫
        kanDiagramJointEvaluation C) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
    (weightedNerveJointComparisonEdge C).toTruncated) :=
      weightedNerveJointComparisonEdge_isInvertible C
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (weightedNerveJointComparisonEdge C).toTruncated)

end SerrePositivity.InfinityCategories
