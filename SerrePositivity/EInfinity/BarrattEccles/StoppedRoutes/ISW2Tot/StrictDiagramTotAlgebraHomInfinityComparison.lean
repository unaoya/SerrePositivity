module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeHomInfinityComparison
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotalizationInput

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じ全Hom比較を、元の全BE代数源・元の同じstrict図式上で読む。
方針：元の全nerve包含を前合成し、全単体の源の一致と同じ評価で照合。
規約：IS-W2 R03の係数移送・自然性の法則。高次自然性を保持する。
使われ方：元の同じ重み付き錐とnative錐の右境界の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotAlgebraHomInfinityModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotAlgebraHomInfinityFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotAlgebraHomInfinityCofibrant (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A X

/-- 元の全代数nerve上の実frame Homは、元のalgebraCAlgSourceの正本Homと全同型。 -/
def strictBEAlgebraProbeHomInfinityIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelUpNerve A) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
            (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A) ≫
        homInfinityCovariant
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeFrameHomInfinityIso A X).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelUpNerve A))
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_up] using h

/-- 元の同じstrict BE図式の全nerveに沿う正本Homとの全比較。 -/
def strictBETotDiagramProbeHomInfinityIso
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelUpNerve A) ≫
          _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
            ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
              (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialDiagram A F) ≫
        homInfinityCovariant
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBEAlgebraProbeHomInfinityIso A X).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F))
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialDiagram] using h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
