module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonArrow
public import SerrePositivity.InfinityCategories.F1.Coherent.ResolutionComparisonEdge

/-!
概要：高次の Hom に関して自然な Kan 値の比較を coherent な関手の比較にする。
方針：二点図式の豊穣的な族を実現して転置し、対象での比較が同値なら可逆な辺にする。
規約：比較する対象の射そのものを各頂点で回収する。
使われ方：Kerodon Corollary 5.6.0.6、共通解像の比較を一般の coherent な図式へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：豊穣な比較を二点を底とする coherent な空間値図式の族にする。
方針：二点図式への豊穣関手を coherent nerve と共同評価で実現する。
規約：始域の対象の宇宙は Kan 複体の対象の宇宙に揃える。
使われ方：Kerodon Corollary 5.6.0.6、比較の族を転置するための実際の射。 -/
noncomputable def kanEnrichedComparisonFamily {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    SimplicialNerve C ⟶ SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2)))) :=
  coherentNerveMap (kanEnrichedComparisonArrowEnriched η) ≫ kanDiagramRealization _

/-- 概要：豊穣な比較の coherent な族を零で評価すると F の coherent nerve。
方針：共同評価と対象の評価の可換式に豊穣関手の零側の公式を続ける。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、coherent な比較の始点。 -/
lemma kanEnrichedComparisonFamily_zero {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    kanEnrichedComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) = coherentNerveMap F := by
  rw [kanEnrichedComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  change coherentNerveMap (kanEnrichedComparisonArrowEnriched η) ≫
    coherentNerveMap (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = _
  rw [← coherentNerveMap_comp, kanEnrichedComparisonArrowEnriched_zero]

/-- 概要：豊穣な比較の coherent な族を一で評価すると G の coherent nerve。
方針：共同評価と対象の評価の可換式に豊穣関手の一側の公式を続ける。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、coherent な比較の終点。 -/
lemma kanEnrichedComparisonFamily_one {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    kanEnrichedComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) = coherentNerveMap G := by
  rw [kanEnrichedComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  change coherentNerveMap (kanEnrichedComparisonArrowEnriched η) ≫
    coherentNerveMap (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = _
  rw [← coherentNerveMap_comp, kanEnrichedComparisonArrowEnriched_one]

/-- 概要：高次の Hom に関して自然な比較は二つの coherent nerve の写像間の辺。
方針：比較の族を転置し、二点の底の標準辺を写す。
規約：端点は F と G の coherent nerve の関手頂点。
使われ方：Kerodon Corollary 5.6.0.6、自然な比較を関手空間の実際の辺として扱う。 -/
noncomputable def kanEnrichedComparisonEdge {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    Edge (functorVertex (coherentNerveMap F)) (functorVertex (coherentNerveMap G)) :=
  (coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (kanEnrichedComparisonFamily η))).ofEq
      (by rw [transposeFunctorFamily_vertex, kanEnrichedComparisonFamily_zero])
      (by rw [transposeFunctorFamily_vertex, kanEnrichedComparisonFamily_one])

/-- 概要：coherent な比較の辺を対象 X で評価すると指定した比較の射の辺。
方針：転置の評価を定値パラメーターの共同評価へ戻し、二点図式の射を計算する。
規約：比較の成分の別の代表へ置き換えない。
使われ方：Kerodon Corollary 5.6.0.6、対象ごとの同値性から全体の関手同型を得る判定。 -/
lemma kanEnrichedComparisonEdge_at {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) (X : C) :
    (functorEdgeAt (kanEnrichedComparisonEdge η) (coherentNerveVertex X)).edge =
      (coherentNerveEdge (η.val X)).edge := by
  change ((coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (kanEnrichedComparisonFamily η))).map
      (evaluateFunctorAt (coherentNerveVertex X))).edge = _
  rw [transposeFunctorFamily_edgeAt]
  change kanDiagramDiagonalSimplex
    (nerve.edgeMk (homOfLE
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))).edge
    ((coherentNerveMap (kanEnrichedComparisonArrowEnriched η)).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex X) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex, kanDiagramDiagonalSimplex_constant]
  exact kanDiagramCoherentNerve_edge (kanEnrichedComparisonDiagram η X) _

/-- 概要：対象ごとに同値な豊穣な比較は coherent な関手の可逆な辺。
方針：任意の始域の頂点を対象で表し、成分の辺の可逆性を点ごとの判定へ適用する。
規約：始域の coherent nerve の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、大域的な coherent な関手同型の構成。 -/
lemma kanEnrichedComparisonEdge_isInvertible {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (hη : ∀ X, IsQCatEquivalence (X := (F.obj X).obj) (Y := (G.obj X).obj) (η.val X)) :
    IsInvertibleEdge (kanEnrichedComparisonEdge η) := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt (kanEnrichedComparisonEdge η).toTruncated).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  change IsInvertibleEdge
    (functorEdgeAt (kanEnrichedComparisonEdge η) (coherentNerveVertex (coherentNerveObject s))).toTruncated
  apply (isInvertibleEdge_congr (kanEnrichedComparisonEdge_at η (coherentNerveObject s))).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence (hη _)

/-- 概要：対象ごとに同値な豊穣な比較は coherent nerve の写像の関手同型。
方針：構成した可逆な辺のホモトピー圏の射を同型として束縛する。
規約：順方向の射は実際の比較の辺の類。
使われ方：Kerodon Corollary 5.6.0.6、解像の自然な比較を任意の coherent な図式へ引き戻す。 -/
noncomputable def kanEnrichedComparisonIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (hη : ∀ X, IsQCatEquivalence (X := (F.obj X).obj) (Y := (G.obj X).obj) (η.val X)) :
    FunctorIso (coherentNerveMap F) (coherentNerveMap G) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk (kanEnrichedComparisonEdge η).toTruncated) :=
    kanEnrichedComparisonEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (kanEnrichedComparisonEdge η).toTruncated)

end SerrePositivity.InfinityCategories
