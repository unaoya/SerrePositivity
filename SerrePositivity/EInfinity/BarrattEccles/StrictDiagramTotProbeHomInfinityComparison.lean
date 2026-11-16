module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeNativeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.VertexIsoUniverseLift

/-!
概要：同じprobe比較を、正本共変Hom関手の全標的の同型として消す。
方針：同じ源の頂点同型を反転・宇宙持ち上げし、元のco-Yonedaで写す。
規約：IS-W2 R03の係数移送則。点ごとの逆を独立に選ばない。
使われ方：元の任意の試験対象の実frame Homとnative全錐の制限の比較。
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
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotProbeHomInfinityModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotProbeHomInfinityFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeHomInfinityCofibrant (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 元のprobe比較は、同じ正本共変Hom関手の全標的で同じ源の同型を与える。 -/
def strictBETotProbeHomInfinitySourceIso (X : (operad A).Algebra) :
    FunctorIso
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (framedLimitProbe A X))))
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex X))) := by
  have h := liftVertexIso.{u+1,u+2} (strictBETotProbeSourceIso A X).op
  have k := h.map (coyonedaInfinityMap (CAlg_R A))
  rw [coyonedaInfinityMap_vertex, coyonedaInfinityMap_vertex] at k
  exact k

/-- 元の任意の試験対象の実frame Homは、同じ正本Hom関手へ全標的で自然同型。 -/
def strictBETotProbeFrameHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
          (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) :=
  (strictBETotFrameHomInfinityIso A (framedLimitProbe A X)).trans
    ((strictBETotProbeHomInfinitySourceIso A X).precomp
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A)))

end SerrePositivity.EInfinity.BarrattEccles
