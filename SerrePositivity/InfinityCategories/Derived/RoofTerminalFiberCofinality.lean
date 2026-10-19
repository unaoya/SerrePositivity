module
public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone
public import SerrePositivity.InfinityCategories.F1B.QuillenA
public import SerrePositivity.InfinityCategories.F1B.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.F1B.CofinalVertexFiberPullback
public import SerrePositivity.InfinityCategories.F1B.WeakContractibility
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-! # 屋根の左ファイブレーションの終対象 fiber の cofinality

概要：終対象の点は right cofinal で、左ファイブレーションの終対象 fiber 包含も同様。
方針：coslice の始対象と終対象上の fiber の可縮性から Quillen A を使い、基底変換する。
規約：底は任意の quasicategory。使われ方：商側の実屋根全空間と固定商 Hom の弱同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- quasicategory の終対象の点の包含は right cofinal。 -/
lemma roofTerminalPoint_isRightCofinal {B : SSet.{u}} [Quasicategory B]
    (t : B _⦋0⦌) (ht : IsTerminalVertex t) :
    IsRightCofinal (SSet.yonedaEquiv.symm t) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro b
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm b)
  have hc := leftFibration_terminalFiber_isContractibleKan p
    (cosliceIdentityCone_isInitialVertex b) ht
  let e := cofinalVertexFiberPullbackIso p t ≪≫
    pullbackSymmetry p (SSet.yonedaEquiv.symm t)
  have he := (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  exact he.weaklyContractible_iff.mp hc.isWeaklyContractible

/-- 終対象上の fiber の包含は、左ファイブレーションに対して right cofinal。 -/
lemma roofLeftFibration_terminalFiber_isRightCofinal {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (t : B _⦋0⦌) (ht : IsTerminalVertex t) :
    IsRightCofinal (vertexFiberι p t) := by
  have h := leftFibration_pullback_isRightCofinal p (SSet.yonedaEquiv.symm t)
    (roofTerminalPoint_isRightCofinal t ht)
  let e := cofinalVertexFiberPullbackIso p t
  have hi := isRightCofinal_of_rightAnodyne e.hom (rightAnodyneExtensions.of_isIso e.hom)
  have hc := hi.comp h
  rw [cofinalVertexFiberPullbackIso_hom_fst] at hc
  exact hc

end SerrePositivity.InfinityCategories
