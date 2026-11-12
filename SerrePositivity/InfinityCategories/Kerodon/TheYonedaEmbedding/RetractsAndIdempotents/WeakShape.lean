module
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：弱い retract の添字 Ret を、二単体の長辺を一点へ潰す商として構成する。
方針：元の長辺の包含と一点への射の pushout の普遍性を使う。
規約：元の二単体と潰した頂点への二つの標準射を保持する。
使われ方：HTT 4.4.5.2・5 の弱い retract 図式と実際の分裂三角形の照合。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 二単体の長辺を一点へ送る元の射。 -/
def longEdgeCollapse : (Δ[1] : SSet.{u}) ⟶ Δ[0] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

/-- 元の二単体の長辺を一点に潰した、弱い retract の添字。 -/
@[kerodon 03Z6]
def WeakShape : SSet.{u} := pushout (stdSimplex.δ (1 : Fin 3)) longEdgeCollapse.{u}

/-- 元の二単体から弱い retract の添字への標準射。 -/
def weakTriangle : (Δ[2] : SSet.{u}) ⟶ WeakShape := pushout.inl _ _

/-- 潰した元の長辺の頂点から弱い retract の添字への標準射。 -/
def weakImagePoint : (Δ[0] : SSet.{u}) ⟶ WeakShape := pushout.inr _ _

/-- 元の長辺と潰した頂点は同じ商の中で厳密に一致する。 -/
lemma weakTriangle_longEdge :
    stdSimplex.δ (1 : Fin 3) ≫ weakTriangle.{u} = longEdgeCollapse ≫ weakImagePoint :=
  pushout.condition

/-- 弱い retract 図式は元の商全体からの単体的写像。 -/
@[kerodon 03YZ]
abbrev WeakRetractionDiagram (X : SSet.{u}) := WeakShape ⟶ X

/-- 長辺が指定した一点となる元の二単体を、元の商へ降ろす。 -/
def weakDesc {X : SSet.{u}} (t : Δ[2] ⟶ X) (v : Δ[0] ⟶ X)
    (h : stdSimplex.δ (1 : Fin 3) ≫ t = longEdgeCollapse ≫ v) :
    WeakRetractionDiagram X := pushout.desc t v h

/-- 元の商から降ろした写像の二単体は、元の同じ二単体そのもの。 -/
lemma weakDesc_triangle {X : SSet.{u}} (t : Δ[2] ⟶ X) (v : Δ[0] ⟶ X)
    (h : stdSimplex.δ (1 : Fin 3) ≫ t = longEdgeCollapse ≫ v) :
    weakTriangle ≫ weakDesc t v h = t := pushout.inl_desc _ _ _

/-- 元の商から降ろした写像の分裂点は、元の同じ指定点そのもの。 -/
lemma weakDesc_imagePoint {X : SSet.{u}} (t : Δ[2] ⟶ X) (v : Δ[0] ⟶ X)
    (h : stdSimplex.δ (1 : Fin 3) ≫ t = longEdgeCollapse ≫ v) :
    weakImagePoint ≫ weakDesc t v h = v := pushout.inr_desc _ _ _

/-- 元の二単体と潰した頂点への制限は、元の弱い retract 図式を一意に決める。 -/
lemma weakDiagram_ext {X : SSet.{u}} {f g : WeakRetractionDiagram X}
    (h : weakTriangle ≫ f = weakTriangle ≫ g)
    (k : weakImagePoint ≫ f = weakImagePoint ≫ g) : f = g :=
  pushout.hom_ext h k

/-- 元の Ret 図式と、同じ二単体・同じ長辺を潰す指定点のデータとの全単射。 -/
def weakDiagramEquiv (X : SSet.{u}) :
    WeakRetractionDiagram X ≃
      {p : ((Δ[2] : SSet.{u}) ⟶ X) × ((Δ[0] : SSet.{u}) ⟶ X) //
        stdSimplex.δ (1 : Fin 3) ≫ p.1 = longEdgeCollapse ≫ p.2} where
  toFun f := ⟨⟨weakTriangle ≫ f, weakImagePoint ≫ f⟩, by
    rw [← Category.assoc, weakTriangle_longEdge, Category.assoc]⟩
  invFun p := weakDesc p.val.1 p.val.2 p.property
  left_inv f := weakDiagram_ext (weakDesc_triangle _ _ _) (weakDesc_imagePoint _ _ _)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (weakDesc_triangle _ _ _) (weakDesc_imagePoint _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
