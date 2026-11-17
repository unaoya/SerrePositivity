module
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimit
public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE右frameの計算関手を、全図式射を持つTot頂点関手として読む。
方針：既存framedLimitFunctorのnerveに、既存のalgebraCAlgSourceを後合成する。
規約：IS-W2 3b-4 R01。end・重み・置換・CAlg模型を作り直さない。
使われ方：strict BE余単体図式の同じ指定native極限錐族の頂点。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- R01：既存の同じ右frameの全計算関手から得る、全BE Tot頂点関手。 -/
def strictBETotVertex :
    nerve (AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A

/-- 同じ全関手の固定図式での頂点は、元の同じframe計算対象の像。 -/
theorem strictBETotVertex_at (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F)) := by
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
    ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory))).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ F)) = _
  rw [nerveMap_app_mk₀]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
