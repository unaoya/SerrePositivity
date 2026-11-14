module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor

/-!
概要：始域で指定した辺を cocartesian に送る、元の相対関手の全部分複体。
方針：元の底上の関手の一次成分に指定辺の保存条件を課す。
規約：元の cocartesian 相対 Hom は、その射影の cocartesian 辺を指定した場合に厳密に一致する。
使われ方：余極限の各項で指定辺を保持した Hom 空間の降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の相対関手の頂点が、指定した辺を標的の cocartesian 辺へ送る条件。 -/
def markedCocartesianFunctorPredicate {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a) _⦋0⦌) : Prop :=
  ∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm v).val.app (Opposite.op ⦋1⦌) e)

/-- 実際の底上の関手の頂点では、指定辺を送る元の条件に一致する。 -/
lemma markedCocartesianFunctorPredicate_vertex {A E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (W : Set (A _⦋1⦌)) (f : A ⟶ E) (hf : f ≫ q = a) :
    markedCocartesianFunctorPredicate q a W (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q a f hf) ↔
      ∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) e) := by
  change (∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a) ⟨f, hf⟩)).val.app
      (Opposite.op ⦋1⦌) e)) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 指定辺の保存条件を持つ相対関手の元の全部分複体。 -/
def markedCocartesianFunctorSpace {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a) (markedCocartesianFunctorPredicate q a W)

/-- 元の標的が inner fibration なら、指定辺を保つ相対関手の空間は quasicategory。 -/
instance markedCocartesianFunctorSpace_quasicategory {A E B : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q] (a : A ⟶ B) (W : Set (A _⦋1⦌)) :
    Quasicategory (markedCocartesianFunctorSpace q a W) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- cocartesian 辺そのものを指定すると、元の全 cocartesian 相対 Hom を厳密に回収する。 -/
lemma markedCocartesianFunctorSpace_cocartesian {A E B : SSet.{u}} (p : A ⟶ B) (q : E ⟶ B) :
    markedCocartesianFunctorSpace q p {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.3.2.2" (partial := component) "仮定：底を共有する二つの単体集合の射と、始域の指定辺集合（Lean は inert 辺を入力で受け取る）。結論：指定辺を標的の余デカルト辺に送る底上の関手が張る充満部分複体（底上の inert 性を固定すると Alg の辺保存条件に一致）。一般化 ∞ operad の構造と inert 辺の集合自体は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex
attribute [cite HA "2.3.2.2" (partial := component) "仮定：底を共有する二つの単体集合の射と、始域の指定辺集合（Lean は inert 辺を入力で受け取る）。結論：指定辺を標的の余デカルト辺に送る底上の関手が張る充満部分複体（底上の inert 性を固定すると Alg の辺保存条件に一致）。一般化 ∞ operad の構造と inert 辺の集合自体は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.1.3.16" (partial := component) "仮定：底への写像 q とその底の指定辺（Lean では planar 条件は不要で、N(∆ᵒᵖ) の inert 辺を明示する）。結論：底上で指定辺を余デカルト辺に送る section の充満部分複体を構成する（A∞ 代数の section 条件に一致）。planar operad と inert 辺の組は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex
attribute [cite HA "4.1.3.16" (partial := component) "仮定：底への写像 q とその底の指定辺（Lean では planar 条件は不要で、N(∆ᵒᵖ) の inert 辺を明示する）。結論：底上で指定辺を余デカルト辺に送る section の充満部分複体を構成する（A∞ 代数の section 条件に一致）。planar operad と inert 辺の組は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.1.3.18" (partial := component) "仮定：共通の底への二つの写像と始域の指定辺（Lean では operadic 条件は不要で、底を Assoc⊗、始域写像を Cut として明示する）。結論：底上で指定辺を余デカルト辺に送る関手の充満部分複体を与える（HA の表示の関手空間の成分に一致）。planar 引き戻しの AlgA∞ との同定は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.1.3.20" (partial := component) "仮定：底への射影 q、半単体圏の神経からの包含とその指定辺（Lean では planar 条件は不要で、HA の inert 辺を明示する）。結論：その包含の上で指定辺を余デカルト辺へ送る相対関手の充満部分複体を与える（非単位的 A∞ 代数の関手空間の成分に一致）。planar operad と inert 辺の組は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.1.3.9" (partial := component) "仮定：同じ底の上の関手と始域の指定辺（Lean では planar 条件は不要で、HA の inert 辺の集合を明示する）。結論：指定辺の像が余デカルトであることを射の条件として表す（底が同じなので inert 保存の条件に一致）。始域の inert 集合を Cut の底から定める構成は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex
attribute [cite HA "4.1.4.2" (partial := component) "仮定：底の上の写像 q と Tⁿᵒᵖ の包含、その指定辺（Lean では planar 条件は不要で、包含と inert 辺を明示する）。結論：底の上で inert 辺を余デカルト辺に送る関手の充満部分複体を与える（HA の関手空間の成分に一致）。Tⁿ とその inert 辺の定義は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.1.4.7" (partial := component) "仮定：共通の底への写像 q と Tⁿᵒᵖ からの写像、始域の指定辺（Lean では Assoc⊗ とその inert 辺を明示する）。結論：HA の表示と同じ、指定辺を余デカルト辺に送る相対関手の充満部分複体を与える。planar 引き戻しからの表示との同定は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.2.2.10" (partial := component) "仮定：共通の底への写像 q、γ と始域の指定辺（Lean では LM⊗、γ と三条件の辺を明示する）。結論：指定辺を余デカルト辺へ送る底上の関手の充満部分複体を与える（A∞ 加群の関手空間の成分に一致）。LM と固定 A のファイバーは含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace
attribute [cite HA "4.2.2.26" (partial := component) "仮定：底上の関手と始域の指定辺 W（Lean では γ が inert に送る全ての辺を明示する）。結論：対応頂点の述語を各 W の辺の像が余デカルトという条件と同定する（マークの保存条件の成分に一致）。混合辺の分解で三条件と同値になる operadic 判定は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex
