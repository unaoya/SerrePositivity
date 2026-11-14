module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEvaluationLifting

/-! # ホモトピー圏上の loop 関手

概要：普遍四角形の終点評価の同値から h C 上の loop 関手を構成する。
方針：終点評価の逆を選び、反対の角を評価する。二つの選択は可逆二胞体で比較する。
規約：自己同値性と suspension との逆性は別に証明する。
使われ方：S3 の Ω と S4 の三角形のシフト。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：loop 四角形の終点評価は quasicategory の同値。
方針：全境界の持ち上げから厳密な切断と可逆二胞体を得る。
規約：順方向の射は終点評価そのもの。
使われ方：loop 関手の図式の選択。 -/
def loopDiagramTargetEquivalence (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)

/-- 概要：安定 ∞ 圏のホモトピー圏上の loop 関手。
方針：終点評価の圏同値の逆の後で四角形の左下を評価する。
規約：h C の通常の関手として定義し、選択の比較を自然同型で与える。
使われ方：S3 の Ω と三角構造のシフト。 -/
def loopFunctor (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    hoFunctor.obj X ⥤ hoFunctor.obj X :=
  (loopDiagramTargetEquivalence X).toHoEquivalence.inverse ⋙
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)).toFunctor

/-- 概要：同じ終点を厳密に保つ二つの loop 図式の選択は関手として同型。
方針：終点評価の trivial Kan fibration に対する二つの持ち上げを比較する。
規約：基底 A は任意の単体集合。
使われ方：loop の全単体に自然な選択比較。 -/
def loopDiagramFamilyIso {A X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) f g h

/-- 概要：二つの loop 図式の選択が与える h C 上の関手は自然同型。
方針：選択の可逆二胞体を左下で評価し、ホモトピー圏の自然同型へ送る。
規約：同じ終点の族に対する任意の二つの選択を比較する。
使われ方：S3 の Ω の選択によらない性質。 -/
def loopFunctorChoiceIso {A X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) :
    (hoFunctor.map f).toFunctor ⋙ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)).toFunctor ≅
      (hoFunctor.map g).toFunctor ⋙
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)).toFunctor := by
  simpa only [CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (loopDiagramFamilyIso f g h)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)).toNatIso

/-- 概要：選んだ loop 図式の族は終点を厳密に保つ。
方針：trivial Kan fibration の逆射は厳密な切断として選ばれている。
規約：単体集合の射の等式。
使われ方：対象ごとに指定した loop 四角形との比較。 -/
lemma loopDiagramTargetEquivalence_inv_target (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (loopDiagramTargetEquivalence X).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1))

/-- 概要：loop 関手の値は任意の指定した loop 四角形の左下と同型。
方針：同じ終点上の図式の fiber は可縮なので、その二つの頂点を比較して左下で評価する。
規約：指定した四角形は全ての零角と押し出し性を持つ。
使われ方：S4 の具体的な fiber 四角形と loop 関手の照合。 -/
def LoopSquare.loopFunctorObjIso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare x) :
    (loopFunctor X).obj (SSet.HomotopyCategory.mk x) ≅
      SSet.HomotopyCategory.mk s.vertex := by
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p x
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ :=
    ⟨(loopDiagramTargetEquivalence X).inv.app (Opposite.op ⦋0⦌) x, by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact ConcreteCategory.congr_hom (NatTrans.congr_app
        (loopDiagramTargetEquivalence_inv_target X) (Opposite.op ⦋0⦌)) x⟩
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨s.diagramVertex, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact (s.diagramVertex_evaluation 1 1).trans s.target_eq⟩
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v) (hc.isTerminalVertex w))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)
  change (loopFunctor X).obj (SSet.HomotopyCategory.mk x) ≅
    SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) s.diagramVertex) at hi
  rw [s.diagramVertex_evaluation] at hi
  exact hi

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.6"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor
