module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedPairVertices

/-!
概要：固定二対象の全単体族の母対応に、指定単位による随伴条件を課す。
方針：元の左右の頂点と実単位を回収し、その条件の全部分複体を取る。
規約：core を取らず、充填性と射影の同値性は別工程で扱う。
使われ方：HTT 5.2.6.2 の対ごとの全関手圏の対応。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全保存関手圏の合成の頂点は元の LR。
方針：core に属する同じ零単体に検証済みの局所計算を適用する。
規約：元の全関手圏の頂点を保持する。
使われ方：単位の終点の厳密な同定。 -/
lemma pairUnitComposition_vertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition C D).app (Opposite.op ⦋0⦌) (v, w) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition_vertex ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex v⟩
    ⟨w, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex w⟩

/-- 概要：母対応の元の左関手。
方針：左単体射影の零単体を元の関手に戻す。
規約：同型への置換をしない。
使われ方：元の単位の始域・終域。 -/
def pairLeftFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D _⦋0⦌) : C.obj ⟶ D.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitLeft C D).app (Opposite.op ⦋0⦌) x)

/-- 概要：母対応の元の右関手。
方針：右単体射影の零単体の反転を解除して関手に戻す。
規約：逆向きの右関手族の元の頂点を使う。
使われ方：指定単位の随伴条件。 -/
def pairRightFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D _⦋0⦌) : D.obj ⟶ C.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitRight C D).app (Opposite.op ⦋0⦌) x))

/-- 概要：母対応の指定単位を元の LR への実際の辺として回収する。
方針：coslice 頂点の辺と共同評価の計算を使う。
規約：元の単位を選び直さない。
使われ方：随伴条件の全部分複体。 -/
def pairUnitEdge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (pairLeftFunctor x ≫ pairRightFunctor x)) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex x)).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex x)).src_eq
  tgt_eq := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex x)).tgt_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex_projection x).trans (pairUnitComposition_vertex _ _)

/-- 概要：母対応の指定単位の h Fun での表示。
方針：元の実際の辺のホモトピー類を取る。
規約：母空間には単位の全単体データが残る。
使われ方：指定単位による随伴判定。 -/
def pairUnitHom {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C.obj) (pairLeftFunctor x ≫ pairRightFunctor x) :=
  SSet.Truncated.HomotopyCategory.homMk (pairUnitEdge x)

/-- 概要：固定二対象の全関手族と指定随伴単位を保持する対応単体集合。
方針：実単位の随伴判定を頂点条件とする全部分複体を取る。
規約：quasicategory 性と両射影の同値性は未主張、core は取らない。
使われ方：対ごとの双対性の対応空間の候補。 -/
def PairAdjointCorrespondence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (F := pairLeftFunctor x) (G := pairRightFunctor x) (pairUnitHom x))

/-- 概要：随伴対応から元の全左関手圏への単体射影。
方針：全部分複体の包含の後に左族を取り出す。
規約：全自然変換を保持する。
使われ方：対ごとの双対性の左射影。 -/
def pairAdjointLeft (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    PairAdjointCorrespondence C D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (F := pairLeftFunctor x) (G := pairRightFunctor x) (pairUnitHom x))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitLeft C D

/-- 概要：随伴対応から元の全右関手圏の反対への単体射影。
方針：同じ包含の後に逆向きの右族を取り出す。
規約：全自然変換の向きを反転する。
使われ方：対ごとの双対性の右射影。 -/
def pairAdjointRight (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    PairAdjointCorrespondence C D ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C).op :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (F := pairLeftFunctor x) (G := pairRightFunctor x) (pairUnitHom x))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitRight C D

/-- 概要：対応の各頂点は指定した元の二関手の実際の随伴を持つ。
方針：全部分複体の頂点条件に指定単位の随伴判定を適用する。
規約：対応の充填性をこの頂点の結論から主張しない。
使われ方：単体射影の随伴としての意味の回収。 -/
def pairAdjointVertexAdjunction {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (x : PairAdjointCorrespondence C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (pairLeftFunctor x.val) (pairRightFunctor x.val) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition (pairUnitHom x.val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
