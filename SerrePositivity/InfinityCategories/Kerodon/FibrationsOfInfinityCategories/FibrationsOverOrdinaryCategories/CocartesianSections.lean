module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：底上の cocartesian な section の全部分単体集合を構成する。
方針：相対関手空間の頂点のうち全ての辺を cocartesian に送るものに制限する。
規約：section の定義には p の充填性を要求せず、quasicategory 性は inner fibration 性から導く。
使われ方：一般の cocartesian fibration の strict transport 表現の値。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories

/-- 概要：相対関手の頂点から実際の底上の関手を回収する。
方針：内部 Hom の頂点と射の全単射の逆写像。
規約：底を保つ等式は別の補題で与える。
使われ方：section の辺の cocartesian 性を実際の射で述べる。 -/
def relativeFunctorOfVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌) : A ⟶ E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm v.val

/-- 概要：射から作った相対関手頂点の回収は元の射。
方針：頂点表示の全単射の往復。
規約：底の可換性の証明に依存しない。
使われ方：section の頂点条件の具体的な検証。 -/
lemma relativeFunctorOfVertex_vertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : A ⟶ E) (hf : f ≫ p = a) :
    relativeFunctorOfVertex p a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a f hf) = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm_apply_apply f

/-- 概要：回収した相対関手は指定された底の図式に重なる。
方針：全ての頂点を実際の底上の射の表示へ戻す。
規約：厳密な底上の等式。
使われ方：section の評価と普遍性の型。 -/
lemma relativeFunctorOfVertex_projection {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌) :
    relativeFunctorOfVertex p a v ≫ p = a := by
  obtain ⟨f, hf, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex p a v
  rw [relativeFunctorOfVertex_vertex]
  exact hf

/-- 概要：相対関手頂点が全ての辺を p-cocartesian な辺へ送るという条件。
方針：回収した実際の関手の一次成分を検査する。
規約：単位辺も含め、全ての一単体を検査する。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J） の strict transport の頂点条件。 -/
def IsCocartesianSection {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌) : Prop :=
  ∀ e : A _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
    ((relativeFunctorOfVertex p a v).app (Opposite.op ⦋1⦌) e)

/-- 概要：底上の cocartesian section の全部分単体集合。
方針：相対関手空間で cocartesian な頂点だけが張る全部分複体を取る。
規約：高次の射は元の関手空間の全ての自然変換を保持する。
使われ方：一般の strict transport の係数となる ∞ 圏。 -/
def cocartesianSections {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) (IsCocartesianSection p a)

/-- 概要：cocartesian section を元の相対関手空間へ含める。
方針：全部分複体の包含。
規約：各次数で単射。
使われ方：section の制限、評価、族の等式の確認。 -/
def cocartesianSectionsι {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    cocartesianSections p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCocartesianSection p a)).ι

/-- 概要：cocartesian section の包含は単射。
方針：全部分複体の包含の単射性。
規約：p の充填性は不要。
使われ方：包含後の等式による section の射の外延性。 -/
instance cocartesianSectionsι_mono {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Mono (cocartesianSectionsι p a) :=
  inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCocartesianSection p a)).ι)

/-- 概要：inner fibration 上の cocartesian section の単体集合は quasicategory。
方針：内部 Hom の inner fibration の fiber と、その全部分複体の充填性を使う。
規約：底とパラメータの quasicategory 性は不要。
使われ方：strict transport の値を QCat の対象にする。 -/
instance cocartesianSections_quasicategory {A E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] (a : A ⟶ B) : Quasicategory (cocartesianSections p a) := by
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  exact inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) (IsCocartesianSection p a) : SSet.{u}))

/-- 概要：section の各頂点は実際に cocartesian な関手を表す。
方針：全部分複体の零単体の条件を取り出す。
規約：頂点の部分型の値を元の相対関手頂点として読む。
使われ方：制限の保存と scaffold の辺の検証。 -/
lemma cocartesianSections_vertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (cocartesianSections p a) _⦋0⦌) : IsCocartesianSection p a v.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
