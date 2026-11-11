module
public import SerrePositivity.KST.SConstruction.ObjectSTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

/-! # 全ての辺を同値に送る図式の圏
概要：Fiore–Pieper の D(m,w) に対応する全同値図式の充満部分単体集合を定義する。
方針：内部 Hom の頂点条件として全辺の可逆性を課す。
規約：図式間の自然変換まで可逆に制限しない。使われ方：Proposition 4.27 の object/core 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：関手頂点の図式が添字の全ての辺を同値に送る条件。
方針：実際の射へ復号して一次単体の像を調べる。
規約：自然変換自体の可逆性ではない。使われ方：D(m,w) の対象。 -/
def IsEquivalenceDiagramVertex {K C : SSet.{u}} (v : ((ihom K).obj C) _⦋0⦌) : Prop :=
  ∀ s : K _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm v).app (Opposite.op ⦋1⦌) s))

/-- 概要：全ての辺を同値に送る図式の quasicategory の底の単体集合。
方針：内部 Hom の全部分複体。
規約：添字 K と標的 C は任意。使われ方：K=Δ[m] で D(m,w)。 -/
def equivalenceDiagrams (K C : SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) IsEquivalenceDiagramVertex

/-- 概要：全同値図式の圏の全図式への包含。
方針：全部分複体の包含。
規約：全単体で単射。使われ方：条件を忘れた式の照合。 -/
def equivalenceDiagramι (K C : SSet.{u}) : equivalenceDiagrams K C ⟶ (ihom K).obj C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalenceDiagramVertex).ι

/-- 概要：全同値図式の圏は標的が quasicategory なら quasicategory。
方針：内部 Hom の全部分複体の一般定理。
規約：添字 K に Kan 性は不要。使われ方：自然同値の可逆性の判定。 -/
instance equivalenceDiagrams_quasicategory (K C : SSet.{u}) [Quasicategory C] :
    Quasicategory (equivalenceDiagrams K C) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) IsEquivalenceDiagramVertex : SSet.{u}))

/-- 概要：実際の図式の関手頂点での条件は元の辺の条件そのもの。
方針：頂点同値の逆律。
規約：標的の quasicategory 性は不要。使われ方：包含と定数図式の構成。 -/
lemma isEquivalenceDiagramVertex_functorVertex {K C : SSet.{u}} (F : K ⟶ C) :
    IsEquivalenceDiagramVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔
      ∀ s : K _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s)) := by
  change (∀ s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C F)).app (Opposite.op ⦋1⦌) s))) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 概要：全同値図式を添字の任意の射で制限する。
方針：内部 Hom の前合成を全部分複体へ持ち上げる。
規約：前合成は全辺を辺に送る。使われ方：D(m,w) の単体的構造。 -/
def equivalenceDiagramReindex {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagrams K C ⟶ equivalenceDiagrams L C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsEquivalenceDiagramVertex
    (equivalenceDiagramι K C ≫ (pre i).app C) (by
      intro v
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm v.val
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      have hF : IsEquivalenceDiagramVertex v.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change IsEquivalenceDiagramVertex (((pre i).app C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv]
      change IsEquivalenceDiagramVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ F))
      apply (isEquivalenceDiagramVertex_functorVertex _).2
      intro s
      exact hF (i.app (Opposite.op ⦋1⦌) s))

/-- 概要：全同値図式の制限は条件を忘れると通常の前合成。
方針：全部分複体への持ち上げの包含の式。
規約：全単体での等号。使われ方：単体的構造の関手法則。 -/
lemma equivalenceDiagramReindex_ι {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagramReindex i C ≫ equivalenceDiagramι L C =
      equivalenceDiagramι K C ≫ (pre i).app C := rfl

/-- 概要：全同値図式を指定した頂点で評価する。
方針：包含の後で内部 Hom の評価を使う。
規約：評価の同値性はまだ含めない。使われ方：D(m,w) の時刻零への評価。 -/
def equivalenceDiagramEvaluation (K C : SSet.{u}) (k : K _⦋0⦌) :
    equivalenceDiagrams K C ⟶ C := equivalenceDiagramι K C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k

private lemma constant_edge_isInvertible {C : SSet.{u}} (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant c 1)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj C) c) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one c)).2 h

private lemma curry_snd_vertex (K C : SSet.{u}) (c : C _⦋0⦌) :
    (curry (snd K C)).app (Opposite.op ⦋0⦌) c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const c : K ⟶ C) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro k
  rfl

/-- 概要：任意の対象を全同値な定数図式へ送る。
方針：第二射影を curry し、恒等辺の可逆性で全部分複体へ持ち上げる。
規約：標的の quasicategory 性は不要。使われ方：D(m,w) の評価の切断。 -/
def equivalenceDiagramConstant (K C : SSet.{u}) : C ⟶ equivalenceDiagrams K C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsEquivalenceDiagramVertex (curry (snd K C)) (by
    intro c
    rw [curry_snd_vertex]
    apply (isEquivalenceDiagramVertex_functorVertex _).2
    intro s
    exact constant_edge_isInvertible c)

/-- 概要：定数図式を含めると第二射影の curry を回収する。
方針：全部分複体への持ち上げの式。
規約：全単体での等号。使われ方：評価と添字制限の計算。 -/
lemma equivalenceDiagramConstant_ι (K C : SSet.{u}) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramι K C = curry (snd K C) := rfl

/-- 概要：定数図式の指定頂点での評価は恒等射。
方針：内部 Hom の評価と第二射影を各次数で計算する。
規約：添字に指定頂点がある場合の厳密な切断。使われ方：評価の頂点の全射性。 -/
lemma equivalenceDiagramConstant_evaluation (K C : SSet.{u}) (k : K _⦋0⦌) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramEvaluation K C k = 𝟙 C := by
  rw [equivalenceDiagramEvaluation, ← Category.assoc, equivalenceDiagramConstant_ι]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro c
  change C.map (𝟙 d) c = c
  exact CategoryTheory.Functor.map_id_apply C d c

end SerrePositivity.KST.SConstruction
