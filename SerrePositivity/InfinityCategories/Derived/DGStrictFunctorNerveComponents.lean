module
public import SerrePositivity.InfinityCategories.Derived.DGStrictFunctorNerve
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Derived.DGOrderedFunctorArrow
/-!
概要：厳密 dg 関手圏の実 nerve 写像は、元の指定関手頂点と指定変換の辺を回収する。
方針：全次数の評価を定値・一変換の順序相単体へ戻し、元の同じ simplex と比較する。
規約：辺と頂点の生の等式。使われ方：元の変換の類の恒等・合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type v)
  [DGCategory R C] [DGCategory R E]
/-- 構成した実関手圏写像の頂点は、元の同じ dg 関手の nerve の頂点そのもの。 -/
lemma dgStrictFunctorNerveMap_vertex (F : DGFunctor R C E) :
    (dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (⟨F⟩ : DGStrictFunctor R C E)) =
      functorVertex (dgNerve.map F) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  change (dgOrderedFunctorDiagramOfFunctor
    ((Functor.const (Fin (n.unop.len + 1))).obj (⟨F⟩ : DGStrictFunctor R C E))).simplex
      s OrderHom.id = s.map F
  exact dgOrderedFunctorSimplex_const F s OrderHom.id
/-- 構成した実関手圏写像の辺は、元の同じ厳密変換ホモトピーの辺そのもの。 -/
lemma dgStrictFunctorNerveMap_edge {F G : DGFunctor R C E} (η : StrictNatTrans F G) :
    (dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show (⟨F⟩ : DGStrictFunctor R C E) ⟶ ⟨G⟩ from η)) =
      (functorEdgeOfSimplicialHomotopy η.homotopy).edge := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  change (dgOrderedFunctorDiagramOfFunctor
    (α.unop.toOrderHom.monotone.functor ⋙
      ComposableArrows.mk₁ (show (⟨F⟩ : DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))).simplex
        s OrderHom.id = η.simplex s α.unop.toOrderHom
  exact (dgOrderedFunctorSimplex_precomp
    (ComposableArrows.mk₁ (show (⟨F⟩ : DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))
    α.unop.toOrderHom s OrderHom.id).trans
      (dgOrderedFunctorArrow_simplex η s α.unop.toOrderHom)
end SerrePositivity.InfinityCategories
