module
public import SerrePositivity.KST.SConstruction.DoubleCofiberGridComparison

/-! # 二重 cofiber 格子による入力族の coherent な同型
概要：零番目の行・列の商の消滅から、一番目の行・列の入力族の関手同型を構成する。
方針：関手圏の格子に二つの三角形 prism を適用し、内部 Hom の交換で族の向きに戻す。
規約：元の入力族そのものを比較する。使われ方：相対 E の中央評価の逆同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 内部 Hom の転置は族全体の関手同型を保つ。 -/
def functorIsoFlip {E A C : SSet.{u}} [Quasicategory C]
    {F G : E ⟶ (ihom A).obj C} (e : FunctorIso F G) :
    FunctorIso (internalHomFlipHomEquiv E A C F) (internalHomFlipHomEquiv E A C G) := by
  have h := VertexIso.map e (internalHomSwapIso E A C).hom
  rw [internalHomSwapIso_functorVertex, internalHomSwapIso_functorVertex] at h
  exact h

/-- 転置した二つの族の関手同型は元の族の関手同型を与える。 -/
def functorIsoOfFlip {E A C : SSet.{u}} [Quasicategory C]
    {F G : E ⟶ (ihom A).obj C}
    (e : FunctorIso (internalHomFlipHomEquiv E A C F) (internalHomFlipHomEquiv E A C G)) :
    FunctorIso F G := by
  have h := functorIsoFlip e
  change FunctorIso
    ((internalHomFlipHomEquiv E A C).symm (internalHomFlipHomEquiv E A C F))
    ((internalHomFlipHomEquiv E A C).symm (internalHomFlipHomEquiv E A C G)) at h
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  exact h

/-- 二重 cofiber 格子の零番目の行・列の商が消えると一番目の入力族は coherent に同型。 -/
def doubleCofiberInputIso {E C : SSet.{u}} [Quasicategory C] [IsStable C]
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C))
    (hr : ∀ e : E _⦋0⦌,
      IsZeroVertex ((doubleCofiberRow J 0 ≫ cofiberApex C).app (Opposite.op ⦋0⦌) e))
    (hc : ∀ e : E _⦋0⦌,
      IsZeroVertex ((doubleCofiberColumn J 0 ≫ cofiberApex C).app (Opposite.op ⦋0⦌) e)) :
    FunctorIso (doubleCofiberRow J 1 ≫ cofiberProjection C)
      (doubleCofiberColumn J 1 ≫ cofiberProjection C) := by
  let R := internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C (doubleCofiberGrid J)
  have hl : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (squareLeftEdge ≫ R))) := by
    exact (congrArg (fun f => IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv f)))
      (doubleCofiberGrid_left J)).mpr (cofiberFamilyInput_edge_isInvertible _ hc)
  have hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ R))) := by
    exact (congrArg (fun f => IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv f)))
      (doubleCofiberGrid_bottom J)).mpr (cofiberFamilyInput_edge_isInvertible _ hr)
  have h := arrowSquareTopRightIso R hl hb
  change FunctorIso
    (squareTopEdge ≫ internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C (doubleCofiberGrid J))
    (squareRightEdge ≫ internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C
      (doubleCofiberGrid J)) at h
  rw [doubleCofiberGrid_top, doubleCofiberGrid_right] at h
  exact functorIsoOfFlip h

end SerrePositivity.KST.SConstruction
