module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagonalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：定義域図式の比較を全対象・全高次・全添字の共同評価へ実現する。
方針：対角比較の二点図式を全単体で束ね、成分の同値性を大域的な関手同型へ移す。
規約：成分の同型だけから図式の同型を推論せず、実際の一つの族を構成する。
使われ方：共同切断図式と strict transport の coherent な比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：添字と全対象の共同単体を、比較の二点図式の単体へ写す。
方針：対角比較の再添字付けの等式を単体的自然性として使う。
規約：底と対象の二つのパラメーターを同時に保持する。
使われ方：比較の共同実現の実際の射。 -/
def relativeSectionJointArrow {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve (ULift.{u} (Fin 2)) where
  app _ := ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase s.1.down) s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, T⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow_reindex η α.unop.toOrderHom.uliftMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T).symm

/-- 概要：共同単体の比較を二点上の空間値図式の族に実現する。
方針：二点図式の coherent nerve に共同実現を合成する。
規約：全パラメーターで一つの実際の射。
使われ方：比較の辺の構成。 -/
def relativeSectionJointComparisonFamily {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 2)))) :=
  relativeSectionJointArrow η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization _

/-- 概要：添字と全 left fibrations 上の切断図式の共同評価。
方針：図式値豊穣関手の coherent nerve を共同評価へ合成する。
規約：直積上の実際の射を明示する。
使われ方：共同の比較の両端の厳密な表示。 -/
def relativeSectionJointEvaluation {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).toEnrichedFunctor) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramJointEvaluation J

/-- 概要：共同族の零端点は元の定義域の共同切断評価。
方針：各単体で対角比較の二点図式の零成分を取る。
規約：全次数での厳密な等式。
使われ方：比較の辺の始点を固定する。 -/
lemma relativeSectionJointComparisonFamily_zero
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) :
    relativeSectionJointComparisonFamily η ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin 2)))) =
      relativeSectionJointEvaluation D := by
  rw [relativeSectionJointComparisonFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched_zero
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalKanComparison η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T)

/-- 概要：共同族の一端点は制限後の共同切断評価。
方針：各単体で対角比較の二点図式の一成分を取る。
規約：全次数での厳密な等式。
使われ方：比較の辺の終点を固定する。 -/
lemma relativeSectionJointComparisonFamily_one
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) :
    relativeSectionJointComparisonFamily η ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (1 : Fin 2)))) =
      relativeSectionJointEvaluation A := by
  rw [relativeSectionJointComparisonFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_evaluate]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched_one
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalKanComparison η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T)

/-- 概要：共同切断評価の間の実際の比較の辺。
方針：共同族を転置し二点添字の標準辺を写す。
規約：両端は共同族の厳密な評価で固定する。
使われ方：成分の可逆性を図式全体へ反映する。 -/
def relativeSectionJointComparisonEdge {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (relativeSectionJointEvaluation D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (relativeSectionJointEvaluation A)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (relativeSectionJointComparisonFamily η))).ofEq
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, relativeSectionJointComparisonFamily_zero])
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, relativeSectionJointComparisonFamily_one])

/-- 関手の辺の頂点評価は、端点の表示によらず同じ一単体を保つ。 -/
lemma functorEdgeAt_edge_eq {P X : SSet.{u}} {F G : P ⟶ X}
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (p : P _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt e p).edge = (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge :=
  SSet.Edge.ofEq_edge _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex p F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex p G)

/-- 辺の端点の表示を変更して写しても、一単体の像は変わらない。 -/
lemma edge_ofEq_map_edge {X Y : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Edge x y) (hx : x = x') (hy : y = y') (f : X ⟶ Y) :
    ((e.ofEq hx hy).map f).edge = (e.map f).edge := rfl

/-- 概要：共同比較を添字と対象で評価すると元の豊穣比較の辺になる。
方針：転置の評価を定値単体へ戻し、対角比較の定値の公式を使う。
規約：一単体そのものの厳密な等式。
使われ方：共同の辺の可逆性を指定成分の同値性から検証する。 -/
lemma relativeSectionJointComparisonEdge_at
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (j : J) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (relativeSectionJointComparisonEdge η)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison
        (η.app (Opposite.op j))).val p)).edge := by
  rw [functorEdgeAt_edge_eq]
  unfold relativeSectionJointComparisonEdge
  rw [edge_ofEq_map_edge]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_edgeAt]
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.edge.down
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve (ULift.{u} (Fin 2))).map (𝟙 (Opposite.op ⦋1⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase c.1.down) c.2)) = _
  rw [Functor.map_id_apply]
  have hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase c.1.down =
      (Functor.const (ULift.{u} (Fin 2))).obj j := rfl
  have hT : c.2 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) 1 := rfl
  rw [hbase, hT, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagonalArrow_constant]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.edge.down
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison (η.app (Opposite.op j))))).app
      (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex_constant]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison (η.app (Opposite.op j))) p) _

/-- 概要：成分が全て同値なら共同切断の比較の実際の辺は可逆。
方針：関手空間の可逆性を全頂点で評価して判定する。
規約：図式全体の等式を成分の等式から推論しない。
使われ方：共同切断の全パラメーターの比較を関手同型へ束ねる。 -/
lemma relativeSectionJointComparisonEdge_isInvertible
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
    (hη : ∀ j (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (relativeSectionJointComparisonEdge η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt
    (relativeSectionJointComparisonEdge η).toTruncated).mpr
  rintro ⟨⟨s⟩, t⟩
  obtain ⟨j, rfl⟩ : ∃ j : J, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j :=
    ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object t]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (relativeSectionJointComparisonEdge_at η j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject t))).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence (hη j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject t))

/-- 概要：共同切断評価の間の全パラメーター上の指定された関手同型。
方針：実際に構成した比較の辺の類を同型として取る。
規約：順方向の射は同じ比較の辺の類。
使われ方：切断図式の共同実現の大域的な比較。 -/
def relativeSectionJointComparisonIso
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
    (hη : ∀ j (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (relativeSectionJointEvaluation D)
      (relativeSectionJointEvaluation A) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
    (relativeSectionJointComparisonEdge η).toTruncated) :=
    relativeSectionJointComparisonEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (relativeSectionJointComparisonEdge η).toTruncated)

/-- 概要：全 left fibrations 上の切断図式の実現は一つの関手同型で比較される。
方針：共同の比較を curry して元の図式値の関手へ戻す。
規約：頂点だけでなく全高次の図式を同時に比較する。
使われ方：straightening と相対表現の大域的な比較。 -/
def relativeSectionRealizationComparisonIso
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
    (hη : ∀ j (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram D).realization
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).realization := by
  have h := (relativeSectionJointComparisonIso η hη).curry
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (curry (_ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram D).toEnrichedFunctor ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramJointEvaluation J))
    (curry (_ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).toEnrichedFunctor ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramJointEvaluation J)) at h
  rw [curry_natural_left, curry_natural_left] at h
  exact h

/-- 概要：全単体の共同切断図式の間の全パラメーター上の関手同型。
方針：同じ実現の比較を二変数の交換で共同図式の向きへ移す。
規約：個々の図式や対象で同型を選び直さない。
使われ方：初頂点写像の局所化に沿う大域的な比較の降下。 -/
def relativeSectionDiagramInfinityComparisonIso
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
    (hη : ∀ j (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity A) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (relativeSectionRealizationComparisonIso η hη)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).hom
  exact e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
