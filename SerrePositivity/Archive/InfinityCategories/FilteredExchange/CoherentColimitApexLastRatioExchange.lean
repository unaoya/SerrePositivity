module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastRawRatio
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawPointDiagonalRatio
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoInverseRatioExchange
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
/-!
概要：元の native 中間像の値と最後辺の比の逆を、同じ中間比較に沿って交換する。
方針：同じ native 終点を比の終点射で読み、一般の前後合成交換則へ代入する。
規約：元の実 prism・全初期値・比と native 比較を保持する。
使われ方：Ncomp の元の第一辺値との貼り合わせ。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "y" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "f" => coherentColimitApexMiddleCoefficientMap B T
local notation "f'" => coherentColimitApexCoefficientMap B T ≫ coherentColimitRawFiberTransport B a
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "n" => Equiv.symm (functorVertexEquiv _ _)
  (NatTrans.app (parametrizedFiberTransport p x y) (Opposite.op ⦋0⦌)
    (coherentColimitRawIntervalVertex B b))
/-- 概要：同じ native 像の値は、元の中間比較の比の終点射への像。
方針：同じ区間頂点の Yoneda 評価で値射を照合する。
規約：元の native 比較を保持。使われ方：比の逆との交換。 -/
lemma coherentColimitApexLastNative_post_value_heq_raw_ratio_target :
    HEq ((coherentColimitApexLastNativeImageIso B T).postcomp V₂)
      ((coherentColimitApexPointedMiddleEndpointIso B T).postcomp
        (coherentColimitApexLastRawValueRatio B T).targetMap) := by
  refine functorIso_postcomp_heq_native_value
    (coherentColimitApexPointedMiddleEndpointIso B T) n
    (coherentColimitApexLastNativeImageIso B T)
    (coherentColimitRawPointDiagonal_native B b f).symm
    (coherentColimitRawPointDiagonal_native B b f').symm
    (coherentColimitApexLastNative_heq_middle_postcomp B T) V₂ ?_
  have hv : NatTrans.app (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b))
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      coherentColimitRawIntervalVertex B b := by
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  exact congrArg (fun z => (functorVertexEquiv _ _).symm
    ((parametrizedFiberTransport p x y).app (Opposite.op ⦋0⦌) z) ≫ V₂) hv.symm
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 概要：元の native 像の値と比の逆は同じ中間比較に沿って交換できる。
方針：元の三端点を比の両端で照合し、同じ交換則を使う。
規約：元の指定値を保持。使われ方：Ncomp の元の二辺値の貼り合わせ。 -/
lemma coherentColimitApexLastNativeValue_inverse_ratio_heq_exchange :
    HEq ((coherentColimitApexLastNativeImageIso B T).postcomp V₂ ≪≫
        (coherentColimitApexLastSquareRawValueRatio B T).symm)
      (((coherentColimitApexLastRawValueRatio B T).precomp f).symm ≪≫
        (coherentColimitApexPointedMiddleEndpointIso B T).postcomp
          (coherentColimitApexLastRawValueRatio B T).sourceMap) := by
  refine functorIso_inverse_ratio_exchange_heq
    (coherentColimitApexPointedMiddleEndpointIso B T)
    (coherentColimitApexLastRawValueRatio B T)
    ((coherentColimitApexLastNativeImageIso B T).postcomp V₂)
    (coherentColimitApexLastSquareRawValueRatio B T) ?_ ?_ rfl
    (coherentColimitApexLastNative_post_value_heq_raw_ratio_target B T)
    (coherentColimitApexLastSquareRawValueRatio_heq_raw_ratio B T)
  · exact (coherentColimitRawPointDiagonal_native_at_yoneda B b f V₂).trans
      (Category.assoc _ _ _)
  · exact (coherentColimitRawPointDiagonal_native_at_yoneda B b f' V₂).trans
      (Category.assoc _ _ _)
end
end SerrePositivity.InfinityCategories.F2
