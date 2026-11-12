module
public import SerrePositivity.KST.Fibration.CoherentTriangleIntervalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：長 Hom の native path 空間に、元の直接端・合成端の境界を厳密に指定する。
方針：元の native path 区間同型の逆へ標準境界を含める。
規約：元の path・宇宙・区間同型を保持する。新たな存在仮定はない。
使われ方：K-6 c4 の指定境界合成二単体族の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 概要：元の native path 空間内の二端点の境界。
方針：同じ区間同型で元の標準境界を戻す。
規約：直接端と全合成端の両方を同じ実写像に保持する。
使われ方：指定合成二単体の部分図式の包含。 -/
def verdierReadoutPathBoundary :
    (boundary 1 : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) :=
  (boundary 1).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.inv

instance : Mono verdierReadoutPathBoundary.{u} := by
  dsimp [verdierReadoutPathBoundary]
  infer_instance

/-- 概要：同じ境界の零端は元の所有する直接 path を全パラメータで回収する。
方針：元の境界端点を同じ区間同型で写し、既存の端点等号を使う。
規約：全次数の写像の厳密等式。
使われ方：相対持ち上げで元の直接端成分を固定する。 -/
theorem verdierReadoutPathBoundary_zero (A : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫ (verdierReadoutPathBoundary.{u} ▷ A) =
      lift (SSet.const (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})))
        (𝟙 A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint, lift_whiskerRight, SSet.const_comp]
  congr 1
  apply congrArg (SSet.const (X := A))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  exact coherentTriangleInterval_up_first

/-- 概要：同じ境界の一端は元の全合成 path を全パラメータで回収する。
方針：同じ境界端点と公開 native path 区間同型の終点回収を使う。
規約：別の合成 path に置き換えない。全次数の厳密等式。
使われ方：相対持ち上げで元の合成端成分を固定する。 -/
theorem verdierReadoutPathBoundary_one (A : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ≫ (verdierReadoutPathBoundary.{u} ▷ A) =
      lift (SSet.const (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))) (𝟙 A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint, lift_whiskerRight, SSet.const_comp]
  congr 1
  apply congrArg (SSet.const (X := A))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_last

end SerrePositivity.KST.Fibration
