module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.DiscreteIndexIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap

/-!
概要：任意の元の非空有限添字族に、元の反復 coherent 積の余極限頂点の積錐を与える。
方針：有限性から標準添字表示を一度選び、元の各因子の図式を厳密に回収する。
規約：元の族を入力とし、選んだ全単射を全宣言で共有する。
使われ方：P_Σ の sifted 閉性で使う一般有限積の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の非空有限添字の標準表示を、全単射と共に一度選ぶ。 -/
def nonemptyFiniteIndexPresentation (J : Type u) [Finite J] [Nonempty J] :
    Σ n : ℕ, J ≃ ULift.{u} (Fin (n + 1)) :=
  ⟨Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndex_exists_equiv J),
    Classical.choice (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndex_exists_equiv J))⟩

/-- 元の非空有限添字族の、同じ標準表示を使う反復 coherent 積図式。 -/
def finiteFamilyCoherentProduct {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  let P := nonemptyFiniteIndexPresentation J
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct P.1 (fun i ↦ G (P.2.symm (ULift.up i)))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
