module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctorNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorArrow
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 構成した実関手圏写像の頂点は、元の同じ dg 関手の nerve の頂点そのもの。 -/
lemma dgStrictFunctorNerveMap_vertex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor
    ((Functor.const (Fin (n.unop.len + 1))).obj (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E))).simplex
      s OrderHom.id = s.map F
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorSimplex_const F s OrderHom.id
/-- 構成した実関手圏写像の辺は、元の同じ厳密変換ホモトピーの辺そのもの。 -/
lemma dgStrictFunctorNerveMap_edge {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy η.homotopy).edge := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor
    (α.unop.toOrderHom.monotone.functor ⋙
      ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))).simplex
        s OrderHom.id = η.simplex s α.unop.toOrderHom
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorSimplex_precomp
    (ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))
    α.unop.toOrderHom s OrderHom.id).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorArrow_simplex η s α.unop.toOrderHom)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
