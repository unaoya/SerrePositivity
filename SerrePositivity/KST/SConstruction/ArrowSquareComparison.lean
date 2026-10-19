module
public import SerrePositivity.KST.SConstruction.ArrowTrianglePrisms
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-! # 左辺と下辺が可逆な四角形の二つの出力辺の比較
概要：上辺と右辺を、対角辺からの二つの coherent な比較で関手同型にする。
方針：三角形 prism の始点で指定された可逆辺、終点で恒等辺を使う。
規約：四角形の押し出し性は仮定しない。使われ方：相対切断の中央評価の逆同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 指定された左辺または下辺が可逆なら三角形 prism は辺全体の関手同型を与える。 -/
def arrowTrianglePrismIso {C : SSet.{u}} [Quasicategory C]
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (b : Bool)
    (hi : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv
      ((if b then squareBottomEdge else squareLeftEdge) ≫ R)))) :
    FunctorIso (arrowSquareDiagonal ≫ R) ((if b then squareRightEdge else squareTopEdge) ≫ R) := by
  have hv (v : (Δ[1] : SSet.{u}) _⦋0⦌) : IsInvertibleEdge (edgeOfSimplex
      ((arrowTrianglePrism b ≫ R).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) := by
    obtain ⟨x, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases x
    · have he := congrArg SSet.yonedaEquiv
        (congrArg (fun f => f ≫ R) (arrowTrianglePrism_source b))
      change (arrowTrianglePrism b ≫ R).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
          PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1) = _ at he
      exact (congrArg (fun s => IsInvertibleEdge (edgeOfSimplex s)) he).mpr hi
    · have he := congrArg SSet.yonedaEquiv
        ((congrArg (fun f => f ≫ R) (arrowTrianglePrism_target b)).trans (SSet.const_comp _ R))
      change (arrowTrianglePrism b ≫ R).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
          PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1) =
        PinchedHom.constant (squareVertex R 1 1) 1 at he
      have hc := isEquivalencePathVertex_const (squareVertex R 1 1)
      unfold IsEquivalencePathVertex at hc
      rw [intervalFunctorVertexEdge_functorVertex] at hc
      exact (congrArg (fun s => IsInvertibleEdge (edgeOfSimplex s)) he).mpr hc
  have e := functorIsoOfEquivalenceHomotopy (arrowTrianglePrism b ≫ R) hv
  change FunctorIso ((prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ arrowTrianglePrism b) ≫ R)
    ((prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ arrowTrianglePrism b) ≫ R) at e
  rw [arrowTrianglePrism_zero, arrowTrianglePrism_one] at e
  exact e

/-- 左辺と下辺が可逆な四角形の上辺と右辺は辺の関手として coherent に同型。 -/
def arrowSquareTopRightIso {C : SSet.{u}} [Quasicategory C]
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hl : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (squareLeftEdge ≫ R))))
    (hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ R)))) :
    FunctorIso (squareTopEdge ≫ R) (squareRightEdge ≫ R) :=
  (arrowTrianglePrismIso R false hl).symm ≪≫ arrowTrianglePrismIso R true hb

end SerrePositivity.KST.SConstruction
