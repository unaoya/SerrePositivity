module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonIndexTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedNaturality

/-!
概要：相対切断の制限の系を全 left fibrations 上の一つの coherent な図式にする。
方針：底上の反変図式の前合成を豊穣比較の図式に束ね、共同評価を実現する。
規約：添字圏の全ての面と退化を一度に保持する。
使われ方：底の単体圏上の共同切断評価から大域的な分類へ進む入力。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：底上の任意の射による切断の前合成は豊穣自然な比較。
方針：相対合成と前合成の可換性を評価表示で使う。
規約：底上の射の可逆性や単射性は要求しない。
使われ方：相対切断の制限を全対象の coherent な図式へ束ねる。 -/
def relativeFunctorOverPreComparison {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a) := by
  refine ⟨fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom f, ?_⟩
  intro p q
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom p.val.hom) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom a p.val q.val) =
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom b p.val q.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q.val.hom f
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom, uncurry_curry]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_overPre f p.val q.val).symm

/-- 概要：底上の反変図式は全 left fibrations 上の豊穣比較の図式を定める。
方針：相対前合成の恒等・合成則を全対象で同時に使う。
規約：普通の圏の図式の高次 nerve を全て実現する。
使われ方：各単体の切断を独立に選ばない高次の共同評価。 -/
def relativeSectionEnrichedDiagram {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) J where
  obj j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (A.obj (Opposite.op j))
  map f := relativeFunctorOverPreComparison (A.map f.op)
  map_id j p := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map (𝟙 (Opposite.op j))) = 𝟙 _
    rw [A.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id p.val.hom _
  map_comp f g p := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map (g.op ≫ f.op)) = _
    rw [A.map_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp p.val.hom _ _

/-- 概要：相対切断の豊穣比較の図式は任意の添字関手の制限を厳密に保つ。
方針：対象と射の定義を同じ合成へ展開する。
規約：単射でない添字関手も含む。
使われ方：面と退化の両方の共同評価の整合性。 -/
lemma relativeSectionEnrichedDiagram_reindex {B : SSet.{u}} {J L : Type u}
    [Category.{u} J] [Category.{u} L] (A : Jᵒᵖ ⥤ Over B) (k : L ⥤ J) :
    (relativeSectionEnrichedDiagram A).reindex k =
      relativeSectionEnrichedDiagram (k.op ⋙ A) := rfl

/-- 概要：底上の図式の全切断を全 left fibrations と同時に coherent に実現する。
方針：切断の豊穣比較の図式の実現を転置する。
規約：全次数の単体的作用を一つの射として定義する。
使われ方：単体圏上の切断の大域的な coherent な系。 -/
def relativeSectionDiagramInfinity {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (relativeSectionEnrichedDiagram A).realization

/-- 概要：共同切断評価の各頂点は元の相対 Hom の豊穣評価の coherent nerve。
方針：転置の頂点公式と図式の実現の評価公式を使う。
規約：対象の関手の頂点の厳密な等式。
使われ方：大域的な切断の系と各単体上の切断を結ぶ。 -/
lemma relativeSectionDiagramInfinity_vertex {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) (j : J) :
    (relativeSectionDiagramInfinity A).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (A.obj (Opposite.op j)))) := by
  rw [relativeSectionDiagramInfinity, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex,
    (relativeSectionEnrichedDiagram A).realization_evaluate]
  rfl

/-- 概要：共同切断評価は任意の添字関手で厳密に自然。
方針：転置と制限の可換性、比較図式の実現の自然性を順に使う。
規約：面と退化について別々の高次の選択をしない。
使われ方：全ての単体の切断評価の面・退化の整合性。 -/
lemma relativeSectionDiagramInfinity_reindex {B : SSet.{u}} {J L : Type u}
    [Category.{u} J] [Category.{u} L] (A : Jᵒᵖ ⥤ Over B) (k : L ⥤ J) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ relativeSectionDiagramInfinity A =
      relativeSectionDiagramInfinity (k.op ⋙ A) := by
  rw [relativeSectionDiagramInfinity, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.transposeFunctorFamily_pre,
    (relativeSectionEnrichedDiagram A).realization_reindex,
    relativeSectionEnrichedDiagram_reindex]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
