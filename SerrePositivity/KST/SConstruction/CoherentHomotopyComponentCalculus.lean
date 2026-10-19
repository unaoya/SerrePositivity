module
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeFunctorImage
public import SerrePositivity.InfinityCategories.F1B.FunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation

/-! # Coherent な円柱と実三角形の成分の計算
概要：後合成と合成三角形を、同じ円柱から取り出した元の一単体へ厳密に戻す。
方針：nerve の自然性と、関手空間の二単体の頂点での評価を使う。
規約：三辺を選び直さず、計算に quasicategory 性を仮定しない。
使われ方：collage 内の合成した成分と元の固定構造射の類の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial

/-- 豊穣関手の nerve は元の通常の射の辺を、元の通常の作用の辺へ写す。 -/
lemma enrichedNerveMap_edge {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (R : EnrichedFunctor SSet.{u} C D) {X Y : C} (f : X ⟶ Y) :
    (coherentNerveMap R).app (Opposite.op ⦋1⦌) (coherentNerveEdge f).edge =
      (coherentNerveEdge ((coherentEnrichedUnderlyingFunctor R).map f)).edge := by
  rw [coherentNerveEdge_edge, coherentNerveEdge_edge]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (nerveToCoherent_postcomp R) (Opposite.op ⦋1⦌))
    (ComposableArrows.mk₁ f)
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, nerveMap_app_mk₁] using h

/-- 通常の図式の豊穣後合成は、各頂点で元の対象の像を回収する。 -/
lemma strictCoherentDiagram_postcomp_vertex {C D : Type v}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    {I : Type u} [SmallCategory I] (F : I ⥤ C)
    (R : EnrichedFunctor SSet.{u} C D) (i : I) :
    (strictCoherentDiagram F ≫ coherentNerveMap R).app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex i)) = coherentNerveVertex (R.obj (F.obj i)) := by
  change (coherentNerveMap R).app _
    ((strictCoherentDiagram F).app _ (ULift.up (nerveVertex i))) = _
  exact (congrArg ((coherentNerveMap R).app (Opposite.op ⦋0⦌))
    (strictCoherentDiagram_vertex F i)).trans (coherentNerveMap_vertex R (F.obj i))

/-- 円柱の後合成は、対象での元の成分の一単体をそのまま写す。 -/
lemma homotopyVertexEdge_postcomp {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) (a : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (functorHomotopyPostcomp H q) a).edge =
      q.app (Opposite.op ⦋1⦌) (simplicialHomotopyVertexEdge H a).edge := rfl

/-- 円柱を curry して頂点で評価すると、同じ元の成分の辺になる。 -/
lemma homotopyVertexEdge_yoneda {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (a : A _⦋0⦌) :
    SSet.yonedaEquiv (curry H.h ≫ evaluateFunctorAt a) =
      (simplicialHomotopyVertexEdge H a).edge := by
  rw [curry_evaluateFunctorAt_vertex]
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant a 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  rw [pinchedConstant_one, hi]
  rfl

/-- 全体の指定三辺の実三角形は、各頂点で同じ三辺の実三角形を与える。 -/
def homotopyCompositionTriangle_vertex {A X : SSet.{u}} {f g h : A ⟶ X}
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (T : FunctorCompositionTriangle l r d) (a : A _⦋0⦌) :
    SSet.Edge.CompStruct (simplicialHomotopyVertexEdge l a)
      (simplicialHomotopyVertexEdge r a) (simplicialHomotopyVertexEdge d a) := by
  refine SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (T.diagram ≫ evaluateFunctorAt a)) ?_ ?_ ?_
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_two]
    exact homotopyVertexEdge_yoneda l a
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_zero]
    exact homotopyVertexEdge_yoneda r a
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_one]
    exact homotopyVertexEdge_yoneda d a

/-- 全体三角形の成分の合成は、同じ成分のホモトピー圏の射の類での合成。 -/
lemma homotopyCompositionTriangle_vertex_hom {A X : SSet.{u}} {f g h : A ⟶ X}
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (T : FunctorCompositionTriangle l r d) (a : A _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge l a).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge r a).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge d a).toTruncated :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (homotopyCompositionTriangle_vertex l r d T a).toTruncated

end SerrePositivity.KST.SConstruction
