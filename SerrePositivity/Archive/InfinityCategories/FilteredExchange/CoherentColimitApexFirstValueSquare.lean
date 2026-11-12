module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexFirstEndpointSquare
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawEdgeValues
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
/-!
概要：元の中間比較と raw 第一辺値の同じ合成を、第一指定対角値と比の逆へ分解する。
方針：同じ raw 辺値とその逆を消去し、第一面の指定正方形を値へ移す。
規約：全初期係数・実両端・元の二因子と指定比較を保持する。
使われ方：元の第一射の評価比較の回収。
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
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "Vfirst" => functorIsoOfEq
  (FunctorIso.precomp (coherentColimitApexRawFirstValueIso B T) q)
  (Eq.symm (Category.assoc q (coherentColimitRawFiberTransport B a) V₁)) rfl

/-- 概要：元の中間比較の値と raw 第一辺値の同じ合成。
方針：元の二因子を保持。規約：指定値を再選択しない。
使われ方：第一射の元の評価比較の回収。 -/
def coherentColimitApexFirstValueComposite :=
  (coherentColimitApexPointedMiddleEndpointIso B T).postcomp V₁ ≪≫ Vfirst
/-- 概要：同じ raw 第一辺値の逆と同じ実対角値の比。
方針：元の二因子を保持。規約：全初期係数を保持。
使われ方：第一辺の値因子の消去。 -/
def coherentColimitApexFirstSquareRawValueRatio :=
  Iso.symm Vfirst ≪≫ (coherentColimitRawPointDiagonalComparison B a q).postcomp V₁
/-- 概要：同じ第一辺値の比を続けると元の第一指定対角値に戻る。
方針：元の辺値を消去し同じ指定正方形を値へ移す。
規約：元の指定値を保持。使われ方：第一辺評価の因子式。 -/
lemma coherentColimitApexFirstValueComposite_trans_ratio :
    coherentColimitApexFirstValueComposite B T ≪≫ coherentColimitApexFirstSquareRawValueRatio B T =
      (coherentColimitApexFirstDiagonalComparison B T).postcomp V₁ := by
  unfold coherentColimitApexFirstValueComposite coherentColimitApexFirstSquareRawValueRatio
  rw [Iso.trans_assoc, Iso.self_symm_id_assoc]
  have h := congrArg (fun e => FunctorIso.postcomp e V₁)
    (coherentColimitApexFirstSpecified_initial_square B T)
  simp only [functorIso_postcomp_trans] at h
  convert h using 1
/-- 概要：元の第一辺値の合成は同じ指定対角値と raw 比の逆。
方針：同じ指定値の比を消去する。規約：二因子を保持。
使われ方：第一射の評価比較への接続。 -/
lemma coherentColimitApexFirstValueComposite_eq_diagonal_ratio :
    coherentColimitApexFirstValueComposite B T =
      (coherentColimitApexFirstDiagonalComparison B T).postcomp V₁ ≪≫
        (coherentColimitApexFirstSquareRawValueRatio B T).symm := by
  have h := congrArg (fun e => e ≪≫ (coherentColimitApexFirstSquareRawValueRatio B T).symm)
    (coherentColimitApexFirstValueComposite_trans_ratio B T)
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h
end
end SerrePositivity.InfinityCategories.F2
