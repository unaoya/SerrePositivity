module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanRelativePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ComparisonFiber

/-!
概要：Kan fibration の strict fiber と path 置換による導来ファイバーの共通の解像。
方針：始域の可逆 path の終点を fiber に固定し、終点評価と相対 path 写像で二方向へ射影する。
規約：二つの射影を実際の自明 Kan fibration として構成する。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の錐の pinched Hom と導来ファイバーの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan fibration の頂点 fiber の Kan 性を型クラスとして利用できる。
方針：Kan fibration の left fibration 性と既存の fiber の Kan 性を使う。
規約：始域と標的自体の Kan 性は不要。
使われ方：Kerodon 4.4.2.3（Tag 019E）、7.5.4.6（Tag 03BB） の fiber の同値判定。 -/
instance fibrationVertexFiber_kanComplex {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (b : B.obj (Opposite.op ⦋0⦌)) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b

/-- 概要：Kan fibration の可逆 path 置換の終点射も Kan fibration。
方針：元の射の引き戻しの第一射影と可逆 path の終点評価を合成する。
規約：両端の Kan 性を明示する。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の導来ファイバーの Kan 性。 -/
instance equivalencePathReplacementMap_fibration_of_kanComplex {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fibration_of_kanComplex _
  have : Fibration (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).2
    exact (MorphismProperty.rlp _).pullback_fst _ _
      ((SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap
  infer_instance

/-- 概要：Kan 複体間の Kan fibration の導来ファイバーも Kan 複体。
方針：path 置換の終点射の Kan fibration 性と fiber の Kan 性を使う。
規約：既存の comparisonFiber の定義のまま扱う。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict fiber との同値データ。 -/
instance fibrationComparisonFiber_kanComplex {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (b : B.obj (Opposite.op ⦋0⦌)) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b) :=
  fibrationVertexFiber_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b

/-- 概要：元の始域の path の終点の像を b に固定した共通の解像。
方針：始域の可逆 path の終点評価と p の合成の頂点 fiber を取る。
規約：path の始点は自由に動く。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の二つの fiber の比較 span の中間空間。 -/
def fibrationFiberPathTotal {E B : SSet.{u}} (p : E ⟶ B)
    (b : B.obj (Opposite.op ⦋0⦌)) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 ≫ p) b

/-- 概要：共通の path 解像から strict fiber への終点評価。
方針：始域の path の終点評価を同じ底の頂点 fiber へ制限する。
規約：固定する底の頂点は b。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict fiber 側への自明な射影。 -/
def fibrationFiberPathStrictProjection {E B : SSet.{u}} (p : E ⟶ B)
    (b : B.obj (Opposite.op ⦋0⦌)) : fibrationFiberPathTotal p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 ≫ p) p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1) rfl b

/-- 概要：始点を保つ相対 path 写像は終点の p による像も保つ。
方針：pullback の第一射影と path の後合成の端点公式を使う。
規約：この可換性は充填性を要求しない。
使われ方：Kerodon 4.5.3.24（Tag 02VM） の導来ファイバー側への射影の底の条件。 -/
lemma relativeEquivalencePathMapAt_zero_replacement {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 ≫ p := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint]

/-- 概要：共通の path 解像から path 置換で定義した導来ファイバーへの射影。
方針：path の像と元の始点を記憶する相対 path 写像を fiber へ制限する。
規約：実際の comparisonFiber の模型に値を持つ。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の導来ファイバー側への自明な射影。 -/
noncomputable def fibrationFiberPathDerivedProjection {E B : SSet.{u}} (p : E ⟶ B)
    (b : B.obj (Opposite.op ⦋0⦌)) : fibrationFiberPathTotal p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 0) (relativeEquivalencePathMapAt_zero_replacement p) b

/-- 概要：共通の path 解像は Kan 複体。
方針：始域の path の終点評価と Kan fibration の合成の fiber の Kan 性を使う。
規約：両端の Kan 性と p の Kan fibration 性を明示する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の二つの射影からのホモトピー同値。 -/
instance fibrationFiberPathTotal_kanComplex {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (b : B.obj (Opposite.op ⦋0⦌)) : KanComplex (fibrationFiberPathTotal p b) := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_fibration_of_kanComplex _
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 ≫ p) := inferInstance
  exact fibrationVertexFiber_kanComplex _ b

/-- 概要：共通の解像から strict fiber への射影は自明 Kan fibration。
方針：可逆 path の終点評価の自明 Kan fibration 性を頂点 fiber へ移す。
規約：p の fibration 性はこの射影だけには不要。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の strict fiber 側の同値。 -/
instance fibrationFiberPathStrictProjection_trivialKanFibration {E B : SSet.{u}}
    [KanComplex E] (p : E ⟶ B) (b : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fibrationFiberPathStrictProjection p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_trivialKanFibration _ _ _ _ b

/-- 概要：共通の解像から導来ファイバーへの射影は自明 Kan fibration。
方針：Kan fibration の相対 path の持ち上げ性を頂点 fiber へ移す。
規約：p の両端の Kan 性と Kan fibration 性を使う。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の導来ファイバー側の同値。 -/
instance fibrationFiberPathDerivedProjection_trivialKanFibration {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (b : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fibrationFiberPathDerivedProjection p b) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p 0
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_trivialKanFibration _ _ _ _ b

/-- 概要：Kan 複体間の Kan fibration の strict fiber と導来ファイバーは圏同値。
方針：共通の path 解像からの二つの自明 Kan fibration の同値を合成する。
規約：同値は実際の path 置換による comparisonFiber との間のもの。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の写像空間の strict fiber 表示から導来表示への移送。 -/
noncomputable def fibrationStrictDerivedFiberEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (b : B.obj (Opposite.op ⦋0⦌)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (fibrationFiberPathStrictProjection p b)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (fibrationFiberPathDerivedProjection p b))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
