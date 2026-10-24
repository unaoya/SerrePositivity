module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalVertexFiberPullback

/-!
概要：標準単体の終点包含を left fibration に沿って引き戻すと right anodyne。
方針：終点 fiber の包含の定理を、その fiber と標準 pullback の同型で移す。
規約：これは終点包含の pullback の場合。一般の right anodyne な射は後続で扱う。
使われ方：Kerodon Example 7.2.3.12 の標準単体の場合の通常の pullback 表示。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体の終点包含の left fibration に沿う pullback は right anodyne。
方針：同じ射の頂点 fiber 表示から厳密な同型を消去する。
規約：全空間の quasicategory 性は要求しない。
使われ方：right cofinality の pullback 安定性の終点の場合。 -/
lemma leftFibration_terminalPoint_pullback_rightAnodyne {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [LeftFibration p] :
    rightAnodyneExtensions
      (pullback.fst p (SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n)))) := by
  let b := stdSimplex.obj₀Equiv.symm (Fin.last n)
  let e := cofinalVertexFiberPullbackIso p b
  apply (rightAnodyneExtensions.cancel_left_of_respectsIso e.hom _).mp
  change rightAnodyneExtensions
    ((cofinalVertexFiberPullbackIso p b).hom ≫ pullback.fst p (SSet.yonedaEquiv.symm b))
  rw [cofinalVertexFiberPullbackIso_hom_fst]
  exact leftFibration_terminalFiber_rightAnodyne p

/-- 概要：標準単体の終点包含の left fibration に沿う pullback は right cofinal。
方針：得られた right anodyne 性を cofinality に渡す。
規約：一般の cofinal な射の pullback 安定性を仮定しない。
使われ方：終点 fiber の計算の標準 pullback 射影での表示。 -/
lemma leftFibration_terminalPoint_pullback_isRightCofinal {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [LeftFibration p] :
    IsRightCofinal
      (pullback.fst p (SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n)))) :=
  isRightCofinal_of_rightAnodyne _ (leftFibration_terminalPoint_pullback_rightAnodyne p)

end SerrePositivity.InfinityCategories
