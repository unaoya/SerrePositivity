module
public import SerrePositivity.KST.SConstruction.CoherentSimplexCompositionEdge

/-! # 三辺を指定した coherent 三角形の写像空間の辺
概要：元の三辺 f・g・h を保つ三角形を、h から f≫g への豊穣 Hom の実辺に戻す。
方針：単体の各面の復号を照合し、対象の表示を元の三角形の三頂点に合わせる。
規約：局所 Kan 性を仮定せず、辺やホモトピーを選び直さない。
使われ方：元の suspension 自然性 square の二つの三角形を復号する。
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

/-- 単体の表示を変えても、その二頂点間の通常の射は依存等号で一致する。 -/
lemma coherentSimplexArrow_heq {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} {s t : (SimplicialNerve C) _⦋n⦌} (h : s = t)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq (coherentSimplexArrow s i j hij) (coherentSimplexArrow t i j hij) := by
  cases h
  rfl

/-- 指定した面が元の射の辺なら、対応する二頂点の復号はその射を回収する。 -/
lemma coherentSimplexArrow_of_edge_face {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) (θ : ⦋1⦌ ⟶ ⦋n⦌)
    (f : s.obj (.mk (ULift.up (θ.toOrderHom 0))) ⟶
      s.obj (.mk (ULift.up (θ.toOrderHom 1))))
    (hf : (SimplicialNerve C).map θ.op s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
    coherentSimplexArrow s (θ.toOrderHom 0) (θ.toOrderHom 1)
      (θ.toOrderHom.monotone (by decide)) = f := by
  have hn := coherentSimplexArrow_naturality s θ 0 1 (by decide)
  have he := coherentSimplexArrow_heq hf 0 1 (by decide)
  exact hn.symm.trans ((eq_of_heq he).trans (coherentSimplexArrow_edge f))

/-- 元の三辺を保持する実三角形が指定する、長辺から合成辺への元の写像空間の辺。 -/
def coherentTriangleMappingEdge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)) :
    (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' X Z h)
      (SimplicialCategory.homEquiv' X Z (f ≫ g)) := by
  rcases T with ⟨s, h₂, h₀, h₁⟩
  have hx : s.obj (.mk (ULift.up 0)) = X :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) h₂
  have hy : s.obj (.mk (ULift.up 1)) = Y :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₂
  have hz : s.obj (.mk (ULift.up 2)) = Z :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentSimplexArrow s 0 1 (by decide) = f :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (2 : Fin 3)) f h₂
  have hg : coherentSimplexArrow s 1 2 (by decide) = g :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (0 : Fin 3)) g h₀
  have hh : coherentSimplexArrow s 0 2 (by decide) = h :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (1 : Fin 3)) h h₁
  let e := coherentSimplexCompositionEdge s 0 1 2 (by decide) (by decide)
  simpa only [hf, hg, hh] using e

end SerrePositivity.KST.SConstruction
