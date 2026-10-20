module
public import SerrePositivity.InfinityCategories.F1B.RightAnodyneTensor
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.F1B.KanSliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Derived.RightFibrationTerminalRepresentation

/-!
概要：関手圏内の slice の始域射影と恒等錐を、同じ実頂点で表示する。
方針：right fibration の内部 Hom と点ごとの終対象性を使う。
規約：パラメータの有限性を要求しない。使われ方：実評価方程式を屋根比較へ戻す。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (K : SSet.{u}) {X : SSet.{u}} (z : X _⦋0⦌)
/-- target slice への全関手の、同じパラメータ関手圏への始域射影。 -/
def roofFunctorSliceProjection :
    (ihom K).obj (sliceOver (SSet.yonedaEquiv.symm z)) ⟶ (ihom K).obj X :=
  (ihom K).map (sliceOverProjection (SSet.yonedaEquiv.symm z))
/-- 全パラメータで同じ恒等錐に定値な関手の実頂点。 -/
def roofFunctorSliceIdentity :
    ((ihom K).obj (sliceOver (SSet.yonedaEquiv.symm z))) _⦋0⦌ :=
  functorVertex (SSet.const (sliceIdentityCone z))
/-- 恒等錐の定数族の始域は、元の終点に定値な同じ関手頂点。 -/
lemma roofFunctorSliceIdentity_projection :
    (roofFunctorSliceProjection K z).app (Opposite.op ⦋0⦌) (roofFunctorSliceIdentity K z) =
      functorVertex (SSet.const (X := K) z) := by
  change functorVertex ((SSet.const (sliceIdentityCone z) : K ⟶ _) ≫
    sliceOverProjection _) = _
  rw [SSet.const_comp, sliceIdentityCone_projection]
/-- 恒等錐の定数族は、全パラメータ関手圏でも終対象。 -/
lemma roofFunctorSliceIdentity_isTerminal [Quasicategory X] :
    IsTerminalVertex (roofFunctorSliceIdentity K z) := by
  apply isTerminalVertex_functorVertex_of_pointwise
  intro k
  change IsTerminalVertex (PinchedHom.constant (sliceIdentityCone z) 0)
  rw [pinchedConstant_zero]
  exact F1B.kanSliceIdentityCone_isTerminalVertex z
/-- 実 slice の全パラメータ始域射影は right fibration。 -/
lemma roofFunctorSliceProjection_rightFibration [Quasicategory X] : RightFibration
  (roofFunctorSliceProjection K z) := by
  dsimp only [roofFunctorSliceProjection]
  infer_instance
/-- 恒等錐の始域の点図式は、元の終点の定値関手の点図式に一致する。 -/
lemma roofFunctorSliceIdentity_point :
    SSet.yonedaEquiv.symm ((roofFunctorSliceProjection K z).app
      (Opposite.op ⦋0⦌) (roofFunctorSliceIdentity K z)) =
    SSet.yonedaEquiv.symm (functorVertex (SSet.const (X := K) z)) :=
  congrArg SSet.yonedaEquiv.symm (roofFunctorSliceIdentity_projection K z)
end SerrePositivity.InfinityCategories
