module
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledTriangleInput
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval

/-!
概要：元の K-B 二胞体の直接 path・合成 path を、F1 の同じ区間座標へ厳密に戻す。
方針：所有する二つの path の有限頂点集合を、公開区間同型の両端へ照合する。
規約：path の代表や標準区間を選び直さない。
使われ方：K-6 c4 の指定二端点上の境界合成を全 path へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 概要：区間始点は元の所有する直接 path を厳密回収する。
方針：同じ有限三頂点の path の集合を計算する。
規約：元の直接 path 自身への等号を保持する。
使われ方：指定境界の零側を元の固定直接端へ照合する。 -/
theorem coherentTriangleInterval_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ComposableArrows.mk₀ coherentTriangleDirectPath.{u} := by
  apply CategoryTheory.Functor.ext (fun i => ?_)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval (ULift.up (0 : Fin 2)) = coherentTriangleDirectPath
  apply SimplicialThickening.Path.ext
  ext ⟨a⟩
  fin_cases a <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval, coherentTriangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath] <;>
    decide

/-- 概要：区間終点は元の所有する二短辺の合成 path を厳密回収する。
方針：公開された全体 path 回収と元の合成 path の集合等号を使う。
規約：元の二短辺の合成自身を保持する。
使われ方：指定境界の一側を元の実合成端へ照合する。 -/
theorem coherentTriangleInterval_last :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        ComposableArrows.mk₀ coherentTriangleFullPath.{u} := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso_inv_last, coherentTriangleFullPath_eq_univ]
  rfl

/-- 概要：宇宙を上げても区間始点は同じ元の直接 path。
方針：同じ持ち上げ区間同型を元の小さい宇宙の回収へ戻す。
規約：全 path の座標を保持する。
使われ方：実読出しと同じ宇宙の二端点境界への代入。 -/
theorem coherentTriangleInterval_up_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}) := by
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  rw [coherentTriangleInterval_first]

end SerrePositivity.KST.Fibration
