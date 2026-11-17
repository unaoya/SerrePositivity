module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotEvaluationLocalization
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotalizationComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitInvariance

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じstrict BE Tot頂点を、objectwise擬同型の∞局所化へ降ろす。
方針：元のframedLimitFunctorの擬同型保存と全関手圏の普遍性。
規約：IS-W2 R05の証明分割。頂点を別の極限候補へ置き換えない。
使われ方：同じ指定錐族の局所化とU比較の左境界。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 同じTot頂点の全関手は元のobjectwise擬同型を反転する。 -/
theorem strictBETotVertex_inverts :
    InvertsEdges (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A) := by
  intro s hs
  obtain ⟨F, G, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  have h := _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_map_weak A
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)).map f)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor_map_quasiIso A (AsSmall.{u} SimplexCategory) f hs)
  apply (isInvertibleEdge_congr (f := ((nerve.edgeMk
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)).map f)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A)).toTruncated) ?_).mpr h
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋1⦌)
    ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory))).app
      (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) = _
  rw [nerveMap_app_mk₁]
  rfl

/-- 元のTot全頂点の、指定局所化からの全延長の存在。 -/
theorem exists_strictBETotLocalizedVertex :
    ∃ V : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A,
      Nonempty (FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ V) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A)) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization_isLocalization A).exists_extension
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex_inverts A)

/-- 指定局所化上の同じ全Tot頂点。 -/
def strictBETotLocalizedVertex : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedVertex A).choose

/-- 元の全図式射を保持する、頂点延長の指定全同型。 -/
def strictBETotLocalizedVertex_factor :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotLocalizedVertex A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A) := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedVertex A).choose_spec.some

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
