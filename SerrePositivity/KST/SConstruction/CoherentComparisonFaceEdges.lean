module
public import SerrePositivity.KST.SConstruction.CoherentComparisonEdgeNaturality
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingRawEdge

/-! # 保存した合成面の全復号辺を元の高次単体から回収
概要：指定面の全二単体の等号から、その同じ豊穣比較辺全体を高次単体の作用で回収する。
方針：合成比較辺の全再添字自然性と、指定三辺への復号の同じ raw 値を合わせる。
規約：対象の表示は依存等号で扱い、辺の選び直しも局所 Kan 性の仮定もしない。
使われ方：三入力の四面体の二切断経路を保存した同じ合成面へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 同じ三角形の一般の比較辺と三辺を指定した復号辺は、全一単体で一致する。 -/
lemma coherentTriangleCompositionEdge_heq {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)) :
    HEq (coherentSimplexCompositionEdge T.simplex 0 1 2 (by decide) (by decide)).edge
      (coherentTriangleMappingEdge f g h T).edge :=
  (coherentTriangleMappingEdge_raw_heq f g h T).symm

/-- 元の単体の等号は、同じ頂点列の合成比較辺全体の依存等号を与える。 -/
lemma coherentSimplexCompositionEdge_heq {n : ℕ}
    {s t : (SimplicialNerve C) _⦋n⦌} (ht : s = t)
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    HEq (coherentSimplexCompositionEdge s i j k hij hjk).edge
      (coherentSimplexCompositionEdge t i j k hij hjk).edge := by
  subst t
  rfl

/-- 元の指定辺の全単体から、その通常射を対象表示に依存せず回収する。 -/
lemma coherentSimplexArrow_specified_heq {n : ℕ}
    (s : (SimplicialNerve C) _⦋n⦌) (θ : ⦋1⦌ ⟶ ⦋n⦌) {X Y : C} (f : X ⟶ Y)
    (hf : (SimplicialNerve C).map θ.op s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
    HEq (coherentSimplexArrow s (θ.toOrderHom 0) (θ.toOrderHom 1)
      (θ.toOrderHom.monotone (by decide))) f := by
  have hx : s.obj (.mk (ULift.up (θ.toOrderHom 0))) = X :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) hf
  have hy : s.obj (.mk (ULift.up (θ.toOrderHom 1))) = Y :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) hf
  subst X
  subst Y
  exact heq_of_eq (coherentSimplexArrow_of_edge_face s θ f hf)

/-- 四面体の指定面から、元の三辺を保つ全比較辺を同じ作用で回収する。 -/
lemma coherentTetrahedronFaceComparison_heq
    (s : (SimplicialNerve C) _⦋3⦌) (j : Fin 4) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h))
    (ht : (SimplicialNerve C).δ j s = T.simplex) :
    HEq (coherentSimplexCompositionEdge s ((SimplexCategory.δ j).toOrderHom 0)
      ((SimplexCategory.δ j).toOrderHom 1) ((SimplexCategory.δ j).toOrderHom 2)
      ((SimplexCategory.δ j).toOrderHom.monotone (by decide))
      ((SimplexCategory.δ j).toOrderHom.monotone (by decide))).edge
      (coherentTriangleMappingEdge f g h T).edge := by
  have hn := coherentSimplexCompositionEdge_naturality s (SimplexCategory.δ j)
    0 1 2 (by decide) (by decide)
  exact (heq_of_eq hn.symm).trans
    ((coherentSimplexCompositionEdge_heq ht 0 1 2 (by decide) (by decide)).trans
      (coherentTriangleCompositionEdge_heq f g h T))

end SerrePositivity.KST.SConstruction
