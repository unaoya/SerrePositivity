module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotRightFrameCoherent
public import SerrePositivity.EInfinity.FrameHom.RightFrameHomInfinity

/-!
概要：同じBE right frameの全標的図式を、同じCAlg源の正本共変Hom関手へ結ぶ。
方針：既存の六辺の全比較に、既存Yoneda比較と同じ局所化二胞体を合成する。
規約：IS-W2 R03の既存全比較の係数移送。点ごとのHom同値で代用しない。
使われ方：元の重み付きframe錐と同じnative錐の全制限の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotHomInfinityModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotHomInfinityFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じ実frame Homの全標的図式と、同じCAlg源に沿う正本Homの全関手同型。 -/
def strictBETotFrameHomInfinityIso (X : (operad A).Algebra) [IsCofibrant X] :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X)
        (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  let c := strictBETotRightFrameCoherentComparison A X
  have h := FrameHom.rightFrameTerminalHomIso
    ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X)
    (rightFrameFamily A) c.2
  exact c.1.trans (by simpa only [strictBETotModelSource_vertex] using h)

end SerrePositivity.EInfinity.BarrattEccles
