module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceKan

/-! # Kan 標的への関手の実辺に沿う評価比較

概要：始域の任意の実辺に沿う評価を、関手空間全体上の一つの可逆二胞体へ束ねる。
方針：評価を始域について curry し、Kan な関手空間内の像の辺を取る。
規約：始域の辺の可逆性は不要。使われ方：実屋根内の辺を全高次の降下族へ写す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 始域の頂点を、関手空間上の評価関手へ送る実単体集合写像。 -/
def roofEvaluationFamily (A Z : SSet.{u}) :
    A ⟶ (ihom ((ihom A).obj Z)).obj Z :=
  curry ((β_ ((ihom A).obj Z) A).hom ≫ (ihom.ev A).app Z)

/-- 始域について curry した評価は、各頂点で既存の固定頂点評価と一致する。 -/
lemma roofEvaluationFamily_vertex (A Z : SSet.{u}) (a : A _⦋0⦌) :
    (roofEvaluationFamily A Z).app (Opposite.op ⦋0⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a) := by
  apply CategoryTheory.Functor.functorHom_ext (F := (ihom A).obj Z) (G := Z)
  intro n s
  apply ConcreteCategory.hom_ext
  intro G
  have hs : s = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst s
  rfl

/-- 始域の任意の実辺は、Kan 標的への全関手の評価を比較する可逆二胞体を与える。 -/
def kanEvaluationEdgeIso {A Z : SSet.{u}} [KanComplex Z] {a b : A _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj A) a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) b) := by
  let t := e.map ((truncation 2).map (roofEvaluationFamily A Z))
  let v : Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom A).obj Z)).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) b)) := {
    edge := t.edge
    src_eq := t.src_eq.trans (roofEvaluationFamily_vertex A Z a)
    tgt_eq := t.tgt_eq.trans (roofEvaluationFamily_vertex A Z b) }
  have : IsIso (Truncated.HomotopyCategory.homMk v) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom ((ihom A).obj Z)).obj Z)) _
  exact asIso (Truncated.HomotopyCategory.homMk v)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
