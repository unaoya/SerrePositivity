module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：全関手族の同じ係数での頂点を、同じ元の共同評価の実射へ厳密に戻す。
方針：関手空間の各単体の評価を計算する。
規約：元の全射と指定係数を保持。使われ方：下側輸送比較の成分の両端。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の全関手族を指定係数で評価した頂点は、同じ係数で制限した実射の頂点。 -/
lemma functorCurry_point_vertex {A T X : SSet.{u}}
    (f : A ⊗ T ⟶ X) (l : T _⦋0⦌) :
    (curry f).app (Opposite.op ⦋0⦌) l = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (𝟙 A) (SSet.const l) ≫ f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
