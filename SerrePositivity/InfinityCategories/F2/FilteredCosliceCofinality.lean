module

public import SerrePositivity.InfinityCategories.F2.CosliceCoproduct
public import SerrePositivity.InfinityCategories.F2.KappaFilteredCoslices
public import SerrePositivity.InfinityCategories.F1B.QuillenA
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：filtered ∞ 圏の有限図式の coslice から元の ∞ 圏への射影は right cofinal。
方針：Quillen A の comma を二つの有限図式の和の coslice と厳密に比較する。
規約：元の頂点射影を使い、comma の弱可縮性を追加仮定しない。
使われ方：filtered 添字の余錐による余極限計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの有限図式の coslice の頂点を揃えた引き戻しは弱可縮。
方針：図式の和の coslice の弱可縮性を実際の引き戻し同型で移す。
規約：両射影は元の指定図式の頂点射影。
使われ方：Quillen A の標準 comma の弱可縮性。 -/
lemma isWeaklyContractible_pullback_cosliceProjections {K L C : SSet.{u}}
    [K.Finite] [L.Finite] [Quasicategory C] [IsFilteredInfinity C]
    (p : K ⟶ C) (q : L ⟶ C) :
    IsWeaklyContractible (pullback (sliceUnderProjection p) (sliceUnderProjection q)) := by
  have h := isWeaklyContractible_sliceUnder_of_filtered (coprod.desc p q)
  have he := (isPrecompositionEquivalence_of_iso
    (cosliceCoproduct_isPullback p q).isoPullback).isWeakHomotopyEquivalence
  exact he.weaklyContractible_iff.mp h

/-- 概要：有限図式の coslice の頂点射影は right cofinal。
方針：各頂点の標準 comma を和の図式の coslice と比較し、Quillen A を適用する。
規約：right cofinal は余極限を計算する向き。
使われ方：filtered 図式の余錐を添字にした余極限の制限。 -/
lemma isRightCofinal_sliceUnderProjection_of_filtered {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] [IsFilteredInfinity C] (p : K ⟶ C) :
    IsRightCofinal (sliceUnderProjection p) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro b
  exact isWeaklyContractible_pullback_cosliceProjections p (SSet.yonedaEquiv.symm b)

end SerrePositivity.InfinityCategories.F2
