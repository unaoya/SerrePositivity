module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramArrow

/-!
概要：共同降下の比較の自然性を単体圏の実際の辺で回収する。
方針：ホモトピー圏の自然同型の正方形を標準辺で評価する。
規約：降下で選んだ既存の同型と比較の辺を変更しない。
使われ方：straightening と底の辺の transport の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：関手同型の成分は実際の辺の像とホモトピー圏で可換。
方針：誘導された自然同型の自然性を辺代表で評価する。
規約：始域と標的は quasicategory とする。
使われ方：共同降下の同型の辺での自然性。 -/
lemma functorIso_app_edge_naturality {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] {F G : X ⟶ Y} (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    SSet.Truncated.HomotopyCategory.homMk (e.map F).toTruncated ≫ (I.app y).hom =
      (I.app x).hom ≫ SSet.Truncated.HomotopyCategory.homMk (e.map G).toTruncated := by
  exact I.toNatIso.hom.naturality (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

/-- 概要：全単体の切断評価の辺は相対前合成の比較そのもの。
方針：共同切断図式の全高次の辺の一致を特殊化する。
規約：単体圏の任意の射を含む。
使われ方：降下の自然性の右辺を既存の切断制限へ戻す。 -/
lemma transportSimplexSectionInfinity_edge {B : SSet.{u}}
    {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : i ⟶ j) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map f.op))).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeSectionDiagramInfinity_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B) f

/-- 概要：共同降下で選んだ同型は単体圏の実際の辺に対して自然。
方針：既存の降下同型の自然性を標準添字の辺へ適用する。
規約：両端の成分は頂点評価に使った同じ同型の成分。
使われ方：両端の fiber 評価と既存 transport を比較する正方形。 -/
lemma leftStraighteningSectionJointDiagram_restrictIso_naturality {B : SSet.{u}}
    {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : i ⟶ j) :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f).map
          ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B)).toTruncated ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))).hom =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).toTruncated :=
  functorIso_app_edge_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f)

/-- 概要：一単体から終点への制限の標準辺は初頂点写像で元の辺に戻る。
方針：二つの初頂点座標の単調写像が恒等射であることを計算する。
規約：元の底の一単体そのものを回収する。
使われ方：降下同型の自然性の左辺を底の transport の辺へ戻す。 -/
lemma transportSimplexFirstVertexMap_terminalRestriction {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) σ)).edge =
      σ := by
  change B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction
      (SimplexCategory.δ (0 : Fin 2)) σ))).op σ = σ
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
      (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction
        (SimplexCategory.δ (0 : Fin 2)) σ)) = 𝟙 ⦋1⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k <;> rfl
  exact (congrArg (fun α : ⦋1⦌ ⟶ ⦋1⦌ ↦ B.map α.op σ) hm).trans
    (by rw [op_id, Functor.map_id_apply])

/-- 概要：一単体から始点への制限の標準辺は初頂点写像で退化辺になる。
方針：二つの初頂点座標がともに零であることを計算する。
規約：退化作用素による実際の一単体で述べる。
使われ方：降下の比較の始点側の自然性。 -/
lemma transportSimplexFirstVertexMap_initialRestriction {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (1 : Fin 2)) σ)).edge =
      B.map (SimplexCategory.σ (0 : Fin 1)).op
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ) := by
  change B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
    (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction
      (SimplexCategory.δ (1 : Fin 2)) σ))).op σ = _
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
      (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction
        (SimplexCategory.δ (1 : Fin 2)) σ)) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k <;> rfl
  refine (congrArg (fun α : ⦋1⦌ ⟶ ⦋1⦌ ↦ B.map α.op σ) hm).trans ?_
  change B.map ((SimplexCategory.δ (1 : Fin 2)).op ≫
    (SimplexCategory.σ (0 : Fin 1)).op) σ = _
  rw [Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
