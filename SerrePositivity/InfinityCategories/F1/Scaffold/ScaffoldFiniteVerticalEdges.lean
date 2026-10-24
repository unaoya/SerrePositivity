module

public import SerrePositivity.InfinityCategories.F1.Scaffold.FinitePrism

public import SerrePositivity.InfinityCategories.Core.PrismVerticalSimplex
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteCocartesianEdge
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteFiberComparison

/-!
概要：有限鎖上の scaffold の最初の係数の prism とその垂直辺。
方針：円柱比較の底への射を計算し、最初の辺の cocartesian 性を全空間へ持ち上げる。
規約：元の全空間の射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の垂直辺の条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：scaffold の最初の係数の prism の各垂直辺は区間への射に関して cocartesian。
方針：垂直辺の底への像を最初の辺と同定し、left fibration と合成の定理を使う。
規約：係数値の Kan 性や fiber 比較の同値性はこの条件には不要。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の第三条件。 -/
lemma scaffoldFiniteScaffoldPrism_vertical_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    IsCocartesianEdge (p ≫ scaffoldFiniteCollapse n)
      (prismVerticalSimplex (scaffoldFiniteScaffoldPrism n F l) x) := by
  apply scaffoldFiniteInitialEdge_comp_isCocartesian n p
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), PinchedHom.constant x 1))
    (scaffoldFiniteScaffoldPrism_projection n p F l h)
  change p.app (Opposite.op ⦋1⦌)
    (prismVerticalSimplex (scaffoldFiniteScaffoldPrism n F l) x) =
      SSet.yonedaEquiv ((stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) at he
  rw [scaffoldFiniteInitialEdge_yoneda] at he
  exact he

end SerrePositivity.InfinityCategories
