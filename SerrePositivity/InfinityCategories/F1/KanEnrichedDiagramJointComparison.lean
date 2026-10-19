module

public import SerrePositivity.InfinityCategories.F1.KanEnrichedDiagramDiagonalComparison
public import SerrePositivity.InfinityCategories.F1.RelativeSectionJointComparison
public import SerrePositivity.InfinityCategories.F1.FunctorSpaceCurrying

/-!
概要：Kan 値豊穣図式の比較を全対象・全高次・全添字の共同評価へ実現する。
方針：対角比較の二点図式を全単体で束ね、成分の同値性を大域的な関手同型へ移す。
規約：成分の同型だけから図式の同型を推論せず、実際の一つの族を構成する。
使われ方：共同図式図式と strict transport の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：添字と全対象の共同単体を、比較の二点図式の単体へ写す。
方針：対角比較の再添字付けの等式を単体的自然性として使う。
規約：底と対象の二つのパラメーターを同時に保持する。
使われ方：比較の共同実現の実際の射。 -/
def KanEnrichedDiagramComparison.jointArrow
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C ⟶
      KanDiagramNerve (ULift.{u} (Fin 2)) where
  app _ := ↾fun s ↦ η.diagonalArrow (kanDiagramSimplexBase s.1.down) s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, T⟩
    exact (KanEnrichedDiagramComparison.diagonalArrow_reindex η α.unop.toOrderHom.uliftMap
      (kanDiagramSimplexBase σ.down) T).symm

/-- 概要：共同単体の比較を二点上の空間値図式の族に実現する。
方針：二点図式の coherent nerve に共同実現を合成する。
規約：全パラメーターで一つの実際の射。
使われ方：比較の辺の構成。 -/
def KanEnrichedDiagramComparison.jointComparisonFamily
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 2)))) :=
  KanEnrichedDiagramComparison.jointArrow η ≫ kanDiagramRealization _

/-- 概要：添字と全対象の Kan 値豊穣図式の共同評価。
方針：図式値豊穣関手の coherent nerve を共同評価へ合成する。
規約：直積上の実際の射を明示する。
使われ方：共同の比較の両端の厳密な表示。 -/
def KanEnrichedDiagram.jointEvaluation {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C ⟶
      SpaceInfinity.{u} :=
  (𝟙 _ ⊗ₘ coherentNerveMap D.toEnrichedFunctor) ≫
    kanDiagramJointEvaluation J

/-- 概要：共同族の零端点は元の定義域の共同図式評価。
方針：各単体で対角比較の二点図式の零成分を取る。
規約：全次数での厳密な等式。
使われ方：比較の辺の始点を固定する。 -/
lemma KanEnrichedDiagramComparison.jointComparisonFamily_zero
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) :
    KanEnrichedDiagramComparison.jointComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) =
      KanEnrichedDiagram.jointEvaluation D := by
  rw [KanEnrichedDiagramComparison.jointComparisonFamily, Category.assoc,
    kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  change (KanEnrichedDiagramComparison.diagonalArrow η (kanDiagramSimplexBase σ.down) T).comp SSet
    (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = _
  exact kanEnrichedComparisonArrowEnriched_zero
    (KanEnrichedDiagramComparison.diagonalKanComparison η (kanDiagramSimplexBase σ.down) T)

/-- 概要：共同族の一端点は制限後の共同図式評価。
方針：各単体で対角比較の二点図式の一成分を取る。
規約：全次数での厳密な等式。
使われ方：比較の辺の終点を固定する。 -/
lemma KanEnrichedDiagramComparison.jointComparisonFamily_one
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) :
    KanEnrichedDiagramComparison.jointComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) =
      KanEnrichedDiagram.jointEvaluation E := by
  rw [KanEnrichedDiagramComparison.jointComparisonFamily, Category.assoc,
    kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  change (KanEnrichedDiagramComparison.diagonalArrow η (kanDiagramSimplexBase σ.down) T).comp SSet
    (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = _
  exact kanEnrichedComparisonArrowEnriched_one
    (KanEnrichedDiagramComparison.diagonalKanComparison η (kanDiagramSimplexBase σ.down) T)

/-- 概要：共同図式評価の間の実際の比較の辺。
方針：共同族を転置し二点添字の標準辺を写す。
規約：両端は共同族の厳密な評価で固定する。
使われ方：成分の可逆性を図式全体へ反映する。 -/
def KanEnrichedDiagramComparison.jointComparisonEdge
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) :
    SSet.Edge (functorVertex (KanEnrichedDiagram.jointEvaluation D))
      (functorVertex (KanEnrichedDiagram.jointEvaluation E)) :=
  (coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (KanEnrichedDiagramComparison.jointComparisonFamily η))).ofEq
      (by rw [transposeFunctorFamily_vertex,
        KanEnrichedDiagramComparison.jointComparisonFamily_zero])
      (by rw [transposeFunctorFamily_vertex,
        KanEnrichedDiagramComparison.jointComparisonFamily_one])

/-- 概要：共同比較を添字と対象で評価すると元の豊穣比較の辺になる。
方針：転置の評価を定値単体へ戻し、対角比較の定値の公式を使う。
規約：一単体そのものの厳密な等式。
使われ方：共同の辺の可逆性を指定成分の同値性から検証する。 -/
lemma KanEnrichedDiagramComparison.jointComparisonEdge_at
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (j : J) (p : C) :
    (functorEdgeAt (KanEnrichedDiagramComparison.jointComparisonEdge η)
      (ULift.up (nerveVertex j), coherentNerveVertex p)).edge =
      (coherentNerveEdge ((η.component j).val p)).edge := by
  rw [functorEdgeAt_edge_eq]
  unfold KanEnrichedDiagramComparison.jointComparisonEdge
  rw [edge_ofEq_map_edge]
  rw [transposeFunctorFamily_edgeAt]
  let c := PinchedHom.constant
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C)
    (ULift.up (nerveVertex j), coherentNerveVertex p) 1
  change kanDiagramDiagonalSimplex coherentResolutionComparisonIndexEdge.edge.down
    ((KanDiagramNerve (ULift.{u} (Fin 2))).map (𝟙 (Opposite.op ⦋1⦌))
      (KanEnrichedDiagramComparison.diagonalArrow η (kanDiagramSimplexBase c.1.down) c.2)) = _
  rw [Functor.map_id_apply]
  have hbase : kanDiagramSimplexBase c.1.down =
      (Functor.const (ULift.{u} (Fin 2))).obj j := rfl
  have hT : c.2 = PinchedHom.constant (coherentNerveVertex p) 1 := rfl
  rw [hbase, hT, KanEnrichedDiagramComparison.diagonalArrow_constant]
  change kanDiagramDiagonalSimplex coherentResolutionComparisonIndexEdge.edge.down
    ((coherentNerveMap (kanEnrichedComparisonArrowEnriched
      (η.component j))).app
      (Opposite.op ⦋1⦌) (PinchedHom.constant (coherentNerveVertex p) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex, kanDiagramDiagonalSimplex_constant]
  exact kanDiagramCoherentNerve_edge (kanEnrichedComparisonDiagram
    (η.component j) p) _

/-- 概要：成分が全て同値なら共同図式の比較の実際の辺は可逆。
方針：関手空間の可逆性を全頂点で評価して判定する。
規約：図式全体の等式を成分の等式から推論しない。
使われ方：共同図式の全パラメーターの比較を関手同型へ束ねる。 -/
lemma KanEnrichedDiagramComparison.jointComparisonEdge_isInvertible
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    IsInvertibleEdge (KanEnrichedDiagramComparison.jointComparisonEdge η) := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt
    (KanEnrichedDiagramComparison.jointComparisonEdge η).toTruncated).mpr
  rintro ⟨⟨s⟩, t⟩
  obtain ⟨j, rfl⟩ : ∃ j : J, s = nerveVertex j :=
    ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  rw [← coherentNerveVertex_object t]
  apply (isInvertibleEdge_congr
    (KanEnrichedDiagramComparison.jointComparisonEdge_at η j (coherentNerveObject t))).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence (hη j (coherentNerveObject t))

/-- 概要：共同図式評価の間の全パラメーター上の指定された関手同型。
方針：実際に構成した比較の辺の類を同型として取る。
規約：順方向の射は同じ比較の辺の類。
使われ方：Kan 値図式の共同実現の大域的な比較。 -/
def KanEnrichedDiagramComparison.jointComparisonIso
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    FunctorIso (KanEnrichedDiagram.jointEvaluation D)
      (KanEnrichedDiagram.jointEvaluation E) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
    (KanEnrichedDiagramComparison.jointComparisonEdge η).toTruncated) :=
    KanEnrichedDiagramComparison.jointComparisonEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (KanEnrichedDiagramComparison.jointComparisonEdge η).toTruncated)

/-- 概要：全対象上のKan 値図式の実現は一つの関手同型で比較される。
方針：共同の比較を curry して元の図式値の関手へ戻す。
規約：頂点だけでなく全高次の図式を同時に比較する。
使われ方：straightening と相対表現の大域的な比較。 -/
def KanEnrichedDiagramComparison.realizationIso
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    FunctorIso D.realization
      E.realization := by
  have h := (KanEnrichedDiagramComparison.jointComparisonIso η hη).curry
  change FunctorIso
    (curry (_ ◁ coherentNerveMap D.toEnrichedFunctor ≫
      kanDiagramJointEvaluation J))
    (curry (_ ◁ coherentNerveMap E.toEnrichedFunctor ≫
      kanDiagramJointEvaluation J)) at h
  rw [curry_natural_left, curry_natural_left] at h
  exact h

/-- 概要：全単体の共同図式図式の間の全パラメーター上の関手同型。
方針：同じ実現の比較を二変数の交換で共同図式の向きへ移す。
規約：個々の図式や対象で同型を選び直さない。
使われ方：初頂点写像の局所化に沿う大域的な比較の降下。 -/
def KanEnrichedDiagramComparison.jointDiagramIso
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    FunctorIso (transposeFunctorFamily D.realization) (transposeFunctorFamily E.realization) := by
  have e := VertexIso.map (KanEnrichedDiagramComparison.realizationIso η hη)
    (internalHomSwapIso (SimplicialNerve C)
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) SpaceInfinity.{u}).hom
  exact e

end SerrePositivity.InfinityCategories
