module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceColimitComparison

/-!
概要：余錐間の辺を、元の全始域余錐の下の余錐として読む。
方針：二点の join と区間の同型、および三因子の再結合を使う。
規約：元の比較辺の全高次成分を保持する。
使われ方：入力図式を固定する filtered 表示の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：余錐間の元の辺を始域余錐全体の余錐へ展開する。
方針：同じ辺の全展開を三因子の join として読む。
規約：辺や余錐を選び直さない。
使われ方：固定入力の下の表示の最終頂点を厳密に指定する。 -/
def edgeUnderCocone {K C : SSet.{u}} {q : K ⟶ C} {w z : JoinCocone q}
    (k : (sliceUnder q).Edge w z) : JoinCocone w.val :=
  ⟨(joinAssociator K Δ[0] Δ[0]).hom ≫
    joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
      sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge), by
    rw [← Category.assoc, joinAssociator_leftPair,
      ← Category.assoc, ← joinMap_comp, Category.id_comp, joinStdSimplexIso_zero_inl,
      ← sliceUnderUncurry_precomp, k.δ_one_yonedaEquiv_symm, sliceUnderUncurry_yoneda]⟩

/-- 概要：展開した余錐の元の全図式への制限は元の終域余錐そのもの。
方針：三因子の外側の対を元の辺の終点へ制限する。
規約：元の全終域余錐の厳密な等式。
使われ方：入力図式の正規化で元の指定余錐を回収する。 -/
lemma edgeUnderCocone_old {K C : SSet.{u}} {q : K ⟶ C} {w z : JoinCocone q}
    (k : (sliceUnder q).Edge w z) :
    ((edgeUnderCocone k).restrict (joinInl K Δ[0])).val = z.val := by
  change joinMap (joinInl K Δ[0]) (𝟙 Δ[0]) ≫
    ((joinAssociator K Δ[0] Δ[0]).hom ≫
      joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
        sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge)) = _
  rw [← Category.assoc, joinAssociator_outerPair,
    ← Category.assoc, ← joinMap_comp, Category.id_comp, joinStdSimplexIso_zero_inr,
    ← sliceUnderUncurry_precomp, k.δ_zero_yonedaEquiv_symm, sliceUnderUncurry_yoneda]

/-- 概要：展開した余錐の始域側の頂点への制限は元の底の比較辺。
方針：三因子の右側の対を取り出して coslice 射影を計算する。
規約：元の実際の辺の全射の等式。
使われ方：元の表示脚と固定入力の同時正規化。 -/
lemma edgeUnderCocone_tip {K C : SSet.{u}} {q : K ⟶ C} {w z : JoinCocone q}
    (k : (sliceUnder q).Edge w z) :
    ((edgeUnderCocone k).restrict (joinInr K Δ[0])).val =
      (edgeCosliceVertex (k.map (sliceUnderProjection q)).toTruncated).val := by
  change joinMap (joinInr K Δ[0]) (𝟙 Δ[0]) ≫
    ((joinAssociator K Δ[0] Δ[0]).hom ≫
      joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
        sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge)) = _
  rw [← Category.assoc, joinAssociator_rightPair,
    ← Category.assoc (joinInr K _), joinInr_joinMap, Category.assoc,
    sliceUnderUncurry_projection, SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
