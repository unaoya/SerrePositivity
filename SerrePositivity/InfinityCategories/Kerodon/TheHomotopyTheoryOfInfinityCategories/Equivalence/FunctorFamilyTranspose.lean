module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber

/-!
概要：内部 Hom に値を取る関手の二つの変数の転置。
方針：uncurry した評価の二入力を交換して再び curry する。
規約：単体集合の閉対称モノイダル構造の操作として定義する。
使われ方：Kerodon §4.5.1（Tag 01DQ）、Corollary 5.6.0.6（Tag 028T）、図式の族から coherent な変換を取り出す。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：A で添字付けた I 上の関手の族を、I で添字付けた A 上の関手の族へ転置する。
方針：共同評価の二入力を対称性で交換する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、二点の図式の族から得る coherent な比較。 -/
def transposeFunctorFamily {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X) :
    I ⟶ (ihom A).obj X :=
  curry ((β_ A I).hom ≫ uncurry F)

/-- 概要：転置した族の頂点は元の族をその頂点で評価した関手を表す。
方針：内部 Hom の各次数で唯一の零頂点への射を使い、評価の公式を計算する。
規約：関手の頂点の厳密な等式。
使われ方：Kerodon §4.5.1（Tag 01DQ）、coherent な比較の始点と終点の同定。 -/
lemma transposeFunctorFamily_vertex {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X)
    (i : I _⦋0⦌) :
    (transposeFunctorFamily F).app (Opposite.op ⦋0⦌) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt i) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：転置した族に沿う辺を一点で評価すると、元の族の定値パラメーターでの評価になる。
方針：内部 Hom の評価と二入力の交換を各一単体で計算する。
規約：端点の表示の等式に依存しない一単体そのものの等式。
使われ方：Kerodon §4.5.1（Tag 01DQ）、coherent な比較の点ごとの可逆性の検証。 -/
lemma transposeFunctorFamily_edgeAt {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X)
    {i j : I _⦋0⦌} (e : SSet.Edge i j) (a : A _⦋0⦌) :
    ((e.map (transposeFunctorFamily F)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)).edge =
      ((F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)).app (Opposite.op ⦋1⦌)
        (𝟙 (Opposite.op ⦋1⦌))) e.edge := by
  change ((F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)).app (Opposite.op ⦋1⦌)
    (𝟙 (Opposite.op ⦋1⦌))) (I.map (𝟙 (Opposite.op ⦋1⦌)) e.edge) = _
  rw [Functor.map_id_apply]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
