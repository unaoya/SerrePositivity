module
public import SerrePositivity.KST.SConstruction.ObjectSVertices
public import SerrePositivity.KST.SConstruction.ArTimeCoordinates
public import SerrePositivity.KST.SConstruction.VariableTimeEquivalence

/-! # 自然同値による object S の単体ホモトピー
概要：完全関手の自然同値は、元の全 gapped object S 構成の射の単体ホモトピーを与える。
方針：時刻を Ar[n] の左端で読み、可変時刻で評価した図式の gapped 性を同型で輸送する。
規約：可逆でない自然変換へ一般化しない。使われ方：Fiore–Pieper Proposition 4.27 の object/core 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped 図式と時刻の単体から可変時刻の gapped 図式の頂点を作る。
方針：始点の図式の gapped 性を可変時刻の関手同型で輸送する。
規約：各単体で選択を加えない。使われ方：object S のホモトピーの単体。 -/
def objectSHomotopyVertex {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated)
    {n : ℕ} (v : (sConstruction n X.carrier) _⦋0⦌) (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (sConstruction n Y.carrier) _⦋0⦌ :=
  gappedObjectVertex (variableTimeImage H (gappedDiagram v) (arTimeCoordinate s))
    ((gappedDiagram_isGapped v).variableTimeImage H hH f.property _)

/-- 概要：ホモトピーの候補単体の実際の図式は可変時刻での評価。
方針：gapped な図式とその頂点の対応の逆律。
規約：厳密な射の等号。使われ方：自然性と両端の回収。 -/
lemma objectSHomotopyVertex_diagram {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated)
    {n : ℕ} (v : (sConstruction n X.carrier) _⦋0⦌) (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    gappedDiagram (objectSHomotopyVertex H hH v s) =
      variableTimeImage H (gappedDiagram v) (arTimeCoordinate s) :=
  gappedDiagram_gappedObjectVertex _ _

/-- 概要：点ごとに可逆な自然変換を object S の各単体で可変時刻に評価する射。
方針：時刻単体を Ar[n] の左端で読み、同型による輸送で gapped 性を保つ。
規約：元の全 gapped 図式を使う。使われ方：単体ホモトピーの実際の prism。 -/
def objectSHomotopyMap {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated) :
    objectSConstruction X.carrier ⊗ Δ[1] ⟶ objectSConstruction Y.carrier where
  app n := ↾fun p => objectSHomotopyVertex H hH p.1 p.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨v, s⟩
    apply gappedDiagram_injective
    change gappedDiagram (objectSHomotopyVertex H hH
        ((objectSConstruction X.carrier).map α v) ((Δ[1]).map α s)) =
      gappedDiagram ((objectSConstruction Y.carrier).map α (objectSHomotopyVertex H hH v s))
    simp only [objectSHomotopyVertex_diagram, gappedDiagram_objectS_map]
    rw [variableTimeImage_pre, arTimeCoordinate_naturality]

/-- 概要：完全関手間の点ごとに可逆な自然変換は object S の射の単体ホモトピーを与える。
方針：可変時刻で評価した prism の定値時刻の両端を回収する。
規約：加法性を仮定せず、既存の object S 関手の射を両端に持つ。
使われ方：自然同値による object S のホモトピー不変性。 -/
def objectSHomotopy {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f.val g.val)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated) :
    SSet.Homotopy (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g) where
  h := objectSHomotopyMap H hH
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply gappedDiagram_injective
    change gappedDiagram (objectSHomotopyVertex H hH v
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n.unop.len)) =
      gappedDiagram ((objectSConstructionFunctor.map f).app n v)
    rw [objectSHomotopyVertex_diagram, arTimeCoordinate_constant, variableTimeImage_zero,
      gappedDiagram_objectSFunctor_map]
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply gappedDiagram_injective
    change gappedDiagram (objectSHomotopyVertex H hH v
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n.unop.len)) =
      gappedDiagram ((objectSConstructionFunctor.map g).app n v)
    rw [objectSHomotopyVertex_diagram, arTimeCoordinate_constant, variableTimeImage_one,
      gappedDiagram_objectSFunctor_map]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：完全関手の関手同型から object S の射の実際の単体ホモトピーを得る。
方針：関手同型を可逆な辺で表し、その点ごとの可逆性を使う。
規約：同型の高次の情報を保持した元の object S 関手。
使われ方：object/core 比較と自明ファイブレーションによる模型の比較。 -/
def objectSHomotopyOfFunctorIso {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) :
    SSet.Homotopy (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g) :=
  objectSHomotopy e.simplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible e.edge e.edge_isInvertible)

end SerrePositivity.KST.SConstruction
