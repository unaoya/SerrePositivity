module
public import SerrePositivity.KST.SConstruction.CoherentSimplexInsertionEdges
public import SerrePositivity.KST.SConstruction.CoherentComparisonFaceEdges

/-! # 保存した二面の比較辺を保つ四面体の豊穣合成辺
概要：四面体の二つの挿入経路の上辺を、元の通常射と指定面の全比較辺の実合成へ照合する。
方針：前二射と後二射の保存面から四頂点と元の射を回収し、全比較辺を再添字自然性で移す。
規約：元の面全体の等号を使い、成分や類の一致に置き換えない。
使われ方：三入力 BF 四面体の二経路を、元の保存済みの実合成比較へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (s : (SimplicialNerve C) _⦋3⦌) {W X Y Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z)
  (Tfg : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge fg))
  (Tgh : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge gh))
  (hfg : (SimplicialNerve C).δ 3 s = Tfg.simplex)
  (hgh : (SimplicialNerve C).δ 0 s = Tgh.simplex)

include f g h fg gh Tfg Tgh hfg hgh

/-- 元の前二射・後二射の全合成面から、四面体の元の四対象を回収する。 -/
lemma coherentTetrahedron_vertices :
    s.obj (.mk (ULift.up 0)) = W ∧ s.obj (.mk (ULift.up 1)) = X ∧
      s.obj (.mk (ULift.up 2)) = Y ∧ s.obj (.mk (ULift.up 3)) = Z := by
  have hw : Tfg.simplex.obj (.mk (ULift.up 0)) = W :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) Tfg.d₂
  have hx : Tgh.simplex.obj (.mk (ULift.up 0)) = X :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) Tgh.d₂
  have hy : Tgh.simplex.obj (.mk (ULift.up 1)) = Y :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) Tgh.d₂
  have hz : Tgh.simplex.obj (.mk (ULift.up 2)) = Z :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) Tgh.d₀
  exact ⟨(congrArg (fun t => t.obj (.mk (ULift.up 0))) hfg).trans hw,
    (congrArg (fun t => t.obj (.mk (ULift.up 0))) hgh).trans hx,
    (congrArg (fun t => t.obj (.mk (ULift.up 1))) hgh).trans hy,
    (congrArg (fun t => t.obj (.mk (ULift.up 2))) hgh).trans hz⟩

/-- 第一経路の上辺は、元の第一射と保存した後二射の全比較辺の実合成。 -/
lemma coherentTetrahedronFirstUpper_heq :
    HEq ((SimplicialCategory.sHom (s.obj (.mk (ULift.up 0)))
      (s.obj (.mk (ULift.up 3)))).δ 0
        (coherentSimplexFirstInsertionTriangle s 0 1 2 3
          (by decide) (by decide) (by decide)).simplex)
      ((eComp SSet W X Z).app (Opposite.op ⦋1⦌)
        ((SSet.Edge.id (SimplicialCategory.homEquiv' W X f)).edge,
          (coherentTriangleMappingEdge g h gh Tgh).edge)) := by
  obtain ⟨hw, hx, hy, hz⟩ := coherentTetrahedron_vertices s f g h fg gh Tfg Tgh hfg hgh
  subst W
  subst X
  subst Y
  subst Z
  have hn := coherentSimplexArrow_naturality s (SimplexCategory.δ (3 : Fin 4))
    0 1 (by decide)
  have ht := coherentSimplexArrow_heq hfg 0 1 (by decide)
  have he := coherentSimplexArrow_specified_heq Tfg.simplex
    (SimplexCategory.δ (2 : Fin 3)) f Tfg.d₂
  have hf : coherentSimplexArrow s 0 1 (by decide) = f :=
    hn.symm.trans (eq_of_heq (ht.trans he))
  have hg : (coherentSimplexCompositionEdge s 1 2 3 (by decide) (by decide)).edge =
      (coherentTriangleMappingEdge g h gh Tgh).edge :=
    eq_of_heq (coherentTetrahedronFaceComparison_heq s 0 g h gh Tgh hgh)
  apply heq_of_eq
  rw [coherentSimplexFirstInsertion_upper, hf, hg]

/-- 第二経路の上辺は、保存した前二射の全比較辺と元の最終射の実合成。 -/
lemma coherentTetrahedronSecondUpper_heq :
    HEq ((SimplicialCategory.sHom (s.obj (.mk (ULift.up 0)))
      (s.obj (.mk (ULift.up 3)))).δ 0
        (coherentSimplexSecondInsertionTriangle s 0 1 2 3
          (by decide) (by decide) (by decide)).simplex)
      ((eComp SSet W Y Z).app (Opposite.op ⦋1⦌)
        ((coherentTriangleMappingEdge f g fg Tfg).edge,
          (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z h)).edge)) := by
  obtain ⟨hw, hx, hy, hz⟩ := coherentTetrahedron_vertices s f g h fg gh Tfg Tgh hfg hgh
  subst W
  subst X
  subst Y
  subst Z
  have hn := coherentSimplexArrow_naturality s (SimplexCategory.δ (0 : Fin 4))
    1 2 (by decide)
  have ht := coherentSimplexArrow_heq hgh 1 2 (by decide)
  have he := coherentSimplexArrow_specified_heq Tgh.simplex
    (SimplexCategory.δ (0 : Fin 3)) h Tgh.d₀
  have hh : coherentSimplexArrow s 2 3 (by decide) = h :=
    hn.symm.trans (eq_of_heq (ht.trans he))
  have hf : (coherentSimplexCompositionEdge s 0 1 2 (by decide) (by decide)).edge =
      (coherentTriangleMappingEdge f g fg Tfg).edge :=
    eq_of_heq (coherentTetrahedronFaceComparison_heq s 3 f g fg Tfg hfg)
  apply heq_of_eq
  rw [coherentSimplexSecondInsertion_upper, hf, hh]

end SerrePositivity.KST.SConstruction
