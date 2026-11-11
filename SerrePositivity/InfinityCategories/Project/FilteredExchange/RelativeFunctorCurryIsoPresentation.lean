module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：既存の相対 curry の指定同型を豊穣作用による同じ指定同型として表示する。
方針：端点の関手頂点表示の変更だけを除く。
規約：指定同型の値を保持。使われ方：元の三角形比較の一点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 既存の指定 curry 同型は同じ頂点同型の豊穣作用の端点表示を変えたもの。 -/
lemma relativeFunctorCurryIso_heq_map {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H H' : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (hH' : H' ≫ p = fst A L ≫ a)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (fst A L ≫ a) H hH)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (fst A L ≫ a) H' hH')) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurryIso p a H H' hH hH' e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurryHom p a L)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurryIso
  have hcast {α β : Sort (u + 1)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 指定頂点同型の端点表示だけを変えても同じ射による像の指定値は保たれる。 -/
lemma vertexIso_map_heq_of_heq {X Y : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x' y') (hx : x = x') (hy : y = y')
    (he : HEq e e') (f : X ⟶ Y) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e' f) := by
  subst x'
  subst y'
  cases eq_of_heq he
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
