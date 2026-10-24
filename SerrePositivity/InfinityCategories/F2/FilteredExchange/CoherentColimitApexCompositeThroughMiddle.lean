module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstAfterLastEvaluation
/-!
概要：元の raw 二辺値全体を同じ実中間係数を経由する三因子へ戻す。
方針：指定対角値の実終点を保持して中間交換を元の四因子式へ適用する。
規約：元の二辺値・全初期係数・実中間と指定値を保持する。
使われ方：Ncomp の同じ二射評価への帰還。
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
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "m" => coherentColimitApexMiddleCoefficientMap B T
local notation "m'" => q ≫ coherentColimitRawFiberTransport B a
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B b) :
  spaceSimplexPointedCoefficients s ⟶ _)
local notation "Γ" => intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
  (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
local notation "R" => coherentColimitApexLastRawValueRatio B T
/-- 概要：元の最後指定対角値の終点は同じ中間係数と比の終点射の合成。
方針：同じ指定点の native 終点式を使う。
規約：全初期係数と値射を保持。使われ方：中間係数での表示。 -/
lemma coherentColimitApexLastDiagonalValue_target_eq_middle_ratio :
    diagonalFiberTransport p m Γ ≫ V₂ = m ≫ (R).targetMap := by
  exact (coherentColimitRawPointDiagonal_native_at_yoneda B b m V₂).trans
    (Category.assoc _ _ _)
/-- 概要：元の最後指定対角値を同じ中間係数で読む表示。
方針：同じ実終点だけを表示変更する。規約：指定値を保持。
使われ方：中間係数での比との合成。 -/
def coherentColimitApexLastMiddleDiagonalValue :=
  functorIsoOfEq ((coherentColimitApexLastDiagonalComparison B T).postcomp V₂) rfl
    (coherentColimitApexLastDiagonalValue_target_eq_middle_ratio B T)
/-- 概要：元の二辺値を同じ中間係数の比と第一辺値で読む三因子。
方針：同じ指定対角値と元の二因子を保持する。
規約：全係数と指定値を保持。使われ方：二射評価の合成。 -/
def coherentColimitApexCompositeValueThroughMiddle :=
  coherentColimitApexLastMiddleDiagonalValue B T ≪≫ (FunctorIso.precomp R m).symm ≪≫
    coherentColimitApexMiddleFirstValueAfterLast B T
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 概要：元の raw 二辺値全体は同じ実中間係数経由の三因子。
方針：元の四因子へ同じ中間交換を貼り合わせる。
規約：元の二辺値と指定値を保持。使われ方：Ncomp の値照合。 -/
lemma coherentColimitApexCompositeValueComposite_heq_through_middle :
    HEq (coherentColimitApexCompositeValueComposite B T)
      (coherentColimitApexCompositeValueThroughMiddle B T) := by
  refine (heq_of_eq
    (coherentColimitApexCompositeValueComposite_eq_last_square_factors B T)).trans ?_
  refine functorIso_inverse_ratio_exchange_paste_heq
    (coherentColimitApexPointedMiddleEndpointIso B T) R
    ((coherentColimitApexLastDiagonalComparison B T).postcomp V₂)
    ((coherentColimitApexLastNativeImageIso B T).postcomp V₂)
    (coherentColimitApexLastSquareRawValueRatio B T)
    (coherentColimitApexFirstValueAfterLast B T)
    (coherentColimitApexLastDiagonalValue_target_eq_middle_ratio B T) ?_
    (coherentColimitApexLastNative_post_value_heq_raw_ratio_target B T)
    (coherentColimitApexLastSquareRawValueRatio_heq_raw_ratio B T)
  exact (coherentColimitRawPointDiagonal_native_at_yoneda B b m' V₂).trans
    (Category.assoc _ _ _)
end
end SerrePositivity.InfinityCategories.F2
