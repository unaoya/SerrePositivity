module

public import SerrePositivity.InfinityCategories.F2.PinchedHomEndpointTransport
public import SerrePositivity.InfinityCategories.F2.PinchedHomTensorIso
public import SerrePositivity.InfinityCategories.F2.LaxPullbackMapping

/-!
概要：lax pullback の二入力・両端の写像空間の直積表示。
方針：引き戻しの端点の等式で揃えて直積の右写像空間を分解する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
/-- 概要：lax pullback の二入力・両端の写像空間の直積表示。
方針：引き戻しの端点の等式で揃えて直積の右写像空間を分解する。
規約：元の頂点と右写像空間の単体の値を保持する。
使われ方：原典の写像空間の四角形への厳密な輸送。 -/
def laxPullbackMappingInputsIso :
    pinchedHom ((pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌) x)
      ((pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌) y) ≅
    pinchedHom ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
        ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗
      pinchedHom ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
        ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y) := pinchedHomTensorIso _ _
/-- 概要：lax pullback の二入力・両端の写像空間の直積表示。
方針：引き戻しの端点の等式で揃えて直積の右写像空間を分解する。
規約：元の頂点と右写像空間の単体の値を保持する。
使われ方：原典の写像空間の四角形への厳密な輸送。 -/
def laxPullbackMappingBaseIso :
    pinchedHom ((arrowEndpointPair C).app (Opposite.op ⦋0⦌)
        ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x))
      ((arrowEndpointPair C).app (Opposite.op ⦋0⦌)
        ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y)) ≅
    pinchedHom (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
        (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y)) ⊗
      pinchedHom (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
        (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)) :=
  pinchedHomIsoOfEq (pullbackSimplex_compat (arrowEndpointPair C) (p ⊗ₘ q) x)
      (pullbackSimplex_compat (arrowEndpointPair C) (p ⊗ₘ q) y) ≪≫
    pinchedHomTensorIso _ _

end SerrePositivity.InfinityCategories.F2
