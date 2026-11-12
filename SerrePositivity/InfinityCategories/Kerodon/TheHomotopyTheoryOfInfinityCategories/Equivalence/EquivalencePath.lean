module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の可逆な辺を頂点とする path の単体集合。
方針：標準区間からの関手単体集合の全部分複体を取る。
規約：標準区間の辺の可逆性で頂点を選ぶ。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM）、Theorem 4.8.4.1（Tag 01JX） の isofibration への還元。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単体集合の射と関手単体集合の頂点の同値。
方針：閉構造の curry' と単位からの射の頂点表示を合成する。
規約：任意の単体集合を扱う。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.5.3（Tag 032Y） の関手の頂点の表示。 -/
def functorVertexEquiv (X Y : SSet.{u}) : (X ⟶ Y) ≃ ((ihom X).obj Y) _⦋0⦌ :=
  curryHomEquiv'.trans (SSet.unitHomEquiv _)

/-- 概要：頂点の同値の順方向は既存の関手頂点の定義。
方針：二つの同値の合成を展開する。
規約：既存の A3a の頂点表示を維持する。
使われ方：Kerodon §4.5.1（Tag 01DQ） の API の整合性。 -/
lemma functorVertexEquiv_apply {X Y : SSet.{u}} (f : X ⟶ Y) :
    functorVertexEquiv X Y f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := rfl

/-- 概要：区間からの関手の頂点が表す標的の一次単体。
方針：頂点を区間からの射へ戻し Yoneda 同値を適用する。
規約：標準区間は Δ[1]。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な辺を選ぶ条件。 -/
def intervalFunctorVertexEdge {Y : SSet.{u}} (v : ((ihom (Δ[1] : SSet.{u})).obj Y) _⦋0⦌) :
    Y _⦋1⦌ := SSet.yonedaEquiv ((functorVertexEquiv Δ[1] Y).symm v)

/-- 概要：射の関手頂点が表す一次単体は元の射の一次単体。
方針：頂点の同値の両逆の等式を使う。
規約：区間からの任意の射。
使われ方：Kerodon §4.5.3（Tag 032Y） の恒等 path の確認。 -/
lemma intervalFunctorVertexEdge_functorVertex {Y : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ Y) :
    intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = SSet.yonedaEquiv f := by
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] Y).symm (functorVertexEquiv Δ[1] Y f)) = _
  rw [Equiv.symm_apply_apply]

/-- 概要：可逆な辺を表す関手頂点の条件。
方針：区間からの関手が与える辺の可逆性を要求する。
規約：ホモトピー圏の可逆性を使う。
使われ方：Kerodon §4.5.3（Tag 032Y） の同値の path の部分複体。 -/
def IsEquivalencePathVertex {Y : SSet.{u}}
    (v : ((ihom (Δ[1] : SSet.{u})).obj Y) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (intervalFunctorVertexEdge v))

/-- 概要：可逆な辺からなる path の単体集合。
方針：区間からの関手単体集合で可逆な辺を表す頂点が張る全部分複体を取る。
規約：辺自体の両端は固定しない。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM）、Theorem 4.8.4.1（Tag 01JX）。 -/
@[kerodon 02BY, kerodon 032Z]
def equivalencePath (Y : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Y) IsEquivalencePathVertex : SSet.{u})

/-- 概要：可逆 path の単体集合から区間からの関手単体集合への包含。
方針：全部分複体の包含を使う。
規約：全次数で単射。
使われ方：Kerodon §4.5.3（Tag 032Y） の path の評価。 -/
def equivalencePathι (Y : SSet.{u}) : equivalencePath Y ⟶ (ihom (Δ[1] : SSet.{u})).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι

/-- 概要：可逆 path の指定端点での評価。
方針：包含の後に関手の頂点での評価を適用する。
規約：i=0 は始点、i=1 は終点。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の二つの射影。 -/
def equivalencePathEndpoint (Y : SSet.{u}) (i : Fin 2) : equivalencePath Y ⟶ Y :=
  equivalencePathι Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)

/-- 概要：定値の区間関手の頂点は可逆 path の頂点。
方針：定値辺が恒等辺であることを使う。
規約：標的に quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の定値 path の切断。 -/
lemma isEquivalencePathVertex_const {Y : SSet.{u}} (y : Y _⦋0⦌) :
    IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : (Δ[1] : SSet.{u}) ⟶ Y)) := by
  unfold IsEquivalencePathVertex
  rw [intervalFunctorVertexEdge_functorVertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1))
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) y) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) y))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one y)).mpr h

/-- 概要：全ての頂点を定値の可逆 path に送る射。
方針：第二射影を curry し、全部分複体へ持ち上げる。
規約：定値 path の各端点は同じ頂点。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の切断。 -/
noncomputable def equivalencePathRefl (Y : SSet.{u}) : Y ⟶ equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsEquivalencePathVertex (curry (snd (Δ[1] : SSet.{u}) Y)) (fun y ↦ by
    change IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : (Δ[1] : SSet.{u}) ⟶ Y))
    exact isEquivalencePathVertex_const y)

/-- 概要：定値 path の各端点の評価は恒等射。
方針：関手単体集合の定値 path を各次数で評価する。
規約：i はどちらの端点でもよい。
使われ方：Kerodon §4.5.3（Tag 032Y） の path への埋め込みの両側射影。 -/
lemma equivalencePathRefl_endpoint (Y : SSet.{u}) (i : Fin 2) :
    equivalencePathRefl Y ≫ equivalencePathEndpoint Y i = 𝟙 Y := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro y
  change Y.map (𝟙 (Opposite.op ⦋d⦌)) y = y
  exact CategoryTheory.Functor.map_id_apply Y _ y

/-- 概要：curry した prism の頂点が表す辺は、その頂点上の垂直辺の像。
方針：単位からの射の逆表示と curry を各次数で計算する。
規約：prism は標準区間を第一因子に置く。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の可逆な path の判定。 -/
lemma intervalFunctorVertexEdge_curry {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (x : A _⦋0⦌) :
    intervalFunctorVertexEdge ((curry H).app (Opposite.op ⦋0⦌) x) =
      H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  rfl

/-- 概要：curry した prism の端点評価は元の prism の端点制限。
方針：内部 Hom の恒等写像での評価を計算する。
規約：i はどちらの端点でもよい。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の path の射影。 -/
lemma curry_evaluateFunctorAt_interval {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (i : Fin 2) :
    curry H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change H.app (Opposite.op ⦋d⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) d, A.map (𝟙 (Opposite.op ⦋d⦌)) x) = _
  rw [CategoryTheory.Functor.map_id_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
