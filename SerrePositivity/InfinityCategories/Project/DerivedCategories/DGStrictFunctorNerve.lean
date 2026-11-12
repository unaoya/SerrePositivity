module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransCompositionDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
/-!
概要：厳密 dg 関手圏の通常の nerve から、元の dg nerve 間の全関手 ∞ 圏へ実写像を作る。
方針：通常の各関手単体と dg 単体を、同じ順序相の全 HA 単体へ送って curry する。
規約：全ての面・退化に整合する。使われ方：元の比較変換の恒等・合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t t'
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 同じ通常の図式の前合成は、任意の単調相選択の合成と単体全体で一致する。 -/
lemma dgOrderedFunctorSimplex_precomp {I : Type t} [Preorder I]
    {J : Type t'} [Preorder J] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) (α : J →o I)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (β : Fin (n + 1) →o J) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor (α.monotone.functor ⋙ F)).simplex s β =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor F).simplex s (α.comp β) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl
variable (R C) (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 元の dg nerve と厳密 dg 関手圏の nerve の直積からの、全単体的な実評価。 -/
def dgStrictFunctorNerveEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E where
  app _ := ↾fun s =>
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor s.2).simplex s.1
      OrderHom.id
  naturality _ _ f := by
    ext s
    have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor s.2).simplex_pullback
      s.1 OrderHom.id f.unop.toOrderHom
    exact (dgOrderedFunctorSimplex_precomp s.2 f.unop.toOrderHom
      (s.1.pullback f.unop.toOrderHom)
      OrderHom.id).trans h
/-- 厳密 dg 関手圏の nerve から、元の dg nerve 間の関手 ∞ 圏への実写像。 -/
def dgStrictFunctorNerveMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) :=
  curry (dgStrictFunctorNerveEvaluation R C E)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
