module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotLocalization
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のstrict BE全評価を、同じobjectwise擬同型の局所化へ降ろす。
方針：各点の既存algebraCAlgSourceによる反転と局所化の全関手普遍性。
規約：IS-W2 R05の因子化。評価比較の同値やBE図式の厳密化は結論しない。
使われ方：指定全錐の右境界と、局所化上のU比較の全評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 同じ全strict BE評価を全図式射のパラメータにcurryする。 -/
def strictBETotDiagramFamily : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramNerve A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) := curry (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluation A)

/-- 点での全評価は元の同じ通常評価のnerveに一致。 -/
theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj j) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋n⦌) _ =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋n⦌) _
  congr 1
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  intro i k f
  change (s.obj i).map (𝟙 j) ≫ (s.map f).app j = (s.map f).app j
  simp

/-- 同じ全評価は指定したobjectwise擬同型を可逆にする。 -/
theorem strictBETotDiagramFamily_inverts :
    InvertsEdges (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A) := by
  intro s hs
  obtain ⟨F, G, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  apply (isInvertibleEdge_iff_evaluateFunctorAt_any _).mpr
  rintro ⟨v⟩
  obtain ⟨j, rfl⟩ := nerveEquiv.symm.surjective v
  have h := _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_map_weak A (f.app j) (hs j)
  apply (isInvertibleEdge_congr (f := ((nerve.edgeMk (f.app j)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A)).toTruncated) ?_).mpr h
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A ≫ evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ j))).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) = _
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily_evaluation]
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋1⦌)
    ((nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj j)).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (f.app j))
  rw [nerveMap_app_mk₁]
  rfl

/-- 元の全strict評価の、指定局所化からの全関手の延長の存在。 -/
theorem exists_strictBETotLocalizedEvaluation :
    ∃ ev : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶
        (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
          (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A),
      Nonempty (FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ ev)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A)) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization_isLocalization A).exists_extension
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily_inverts A)

/-- 同じ全図式射を持つ局所化上の実評価。 -/
def strictBETotLocalizedEvaluation : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedEvaluation A).choose

/-- 延長の指定全同型は元の全strict評価を保持する。 -/
def strictBETotLocalizedEvaluation_factor :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotLocalizedEvaluation A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramFamily A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedEvaluation A).choose_spec.some

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
