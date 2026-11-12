module
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingRawEdge
public import SerrePositivity.KST.SConstruction.CoherentTriangleFullPathValues
public import SerrePositivity.KST.Spectra.CoherentSimplexTraces

/-! # 元の三角形の Hom 区間は既存の同じ復号辺
概要：Path 座標で取り出した区間と、三辺を指定して復号した元の実辺を照合する。
方針：零フラグの端点 Path と一フラグの全 Path を同じ包含辺へ同定する。
規約：区間や辺の代表を選び直さず、局所 Kan 性も使わない。
使われ方：合成 prism の外側区間を元の K 適合円柱の二脚へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二単体の Path 区間の零フラグは、元の二端点 Path そのもの。 -/
lemma triangleFlaggedPath_zero :
    flaggedPath (fun _ : Fin 1 => (0 : Fin 2)) =
      coherentEndpointPath (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide) := by
  apply SimplicialThickening.Path.ext
  ext x
  obtain ⟨x⟩ := x
  fin_cases x <;> simp [flaggedPath, coherentEndpointPath]

/-- 二単体の Path 区間の一フラグは、元の二辺の合成 Path そのもの。 -/
lemma triangleFlaggedPath_one :
    flaggedPath (fun _ : Fin 1 => (1 : Fin 2)) =
      coherentEndpointPathComposite
        (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
        (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide) := by
  apply coherentTrianglePath_eq_composite
  exact Or.inr (Or.inr ⟨0, rfl, rfl⟩)

/-- 元の Path 区間は、同じ端点から全 Path への包含辺の Yoneda 表示。 -/
lemma trianglePathInterval_original_edge :
    trianglePathInterval.{u} = SSet.yonedaEquiv.symm
      (nerve.edgeMk (coherentEndpointPathToComposite
        (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
        (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))).edge := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  refine ComposableArrows.ext₁ triangleFlaggedPath_zero triangleFlaggedPath_one ?_
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

/-- 元の coherent 二単体の Hom 区間は、同じ長辺から二辺への指定復号辺。 -/
lemma coherentTriangleTrace_composition_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    triangleTrace s = SSet.yonedaEquiv.symm
      (coherentSimplexCompositionEdge s 0 1 2 (by decide) (by decide)).edge := by
  rw [triangleTrace, trianglePathInterval_original_edge, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 対象を指定した同じ三角形でも、元の Hom 区間は既存の同じ復号辺である。 -/
lemma coherentTriangleTrace_specified_edge_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)) :
    HEq (triangleTrace T.simplex)
      (SSet.yonedaEquiv.symm (coherentTriangleMappingEdge f g h T).edge) := by
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
  subst f
  subst g
  subst h
  apply heq_of_eq
  rw [coherentTriangleTrace_composition_edge]
  rfl

/-- 同じ終域の表示だけを移した全単体写像は、元の写像と依存等号で一致する。 -/
lemma simplicialHom_post_eqToHom_heq {A B D : SSet.{u}} (f : A ⟶ B) (h : B = D) :
    HEq (f ≫ eqToHom h) f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 共通の元の Hom へ対象表示を合わせると、三角形の区間は既存復号辺と厳密に等しい。 -/
lemma coherentTriangleTrace_specified_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h))
    (e : SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 2))) = SimplicialCategory.sHom X Z) :
    triangleTrace T.simplex ≫ eqToHom e =
      SSet.yonedaEquiv.symm (coherentTriangleMappingEdge f g h T).edge :=
  eq_of_heq ((simplicialHom_post_eqToHom_heq (triangleTrace T.simplex) e).trans
    (coherentTriangleTrace_specified_edge_heq f g h T))

/-- 元の同じ指定三角形を面として回収すれば、その区間も同じ復号辺を回収する。 -/
lemma coherentTriangleTrace_specified_face
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (T : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h))
    {s : (SimplicialNerve C) _⦋2⦌} (hs : s = T.simplex)
    (e : SimplicialCategory.sHom (s.obj (.mk (ULift.up 0)))
      (s.obj (.mk (ULift.up 2))) = SimplicialCategory.sHom X Z) :
    triangleTrace s ≫ eqToHom e =
      SSet.yonedaEquiv.symm (coherentTriangleMappingEdge f g h T).edge := by
  subst s
  exact coherentTriangleTrace_specified_edge f g h T e

end SerrePositivity.KST.SConstruction
