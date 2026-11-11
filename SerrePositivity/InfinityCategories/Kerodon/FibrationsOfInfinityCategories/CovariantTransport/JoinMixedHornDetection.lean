module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinExtremeFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalProjection
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：左右の因子がともに現れる join への射は内ホーンへの制限で決まる。
方針：内ホーンに含まれる最初・最後の面から両因子を復元する。
規約：始域は標準単体で、区間への射影または切断を固定する。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、区間付き対角に沿う内ホーンの持ち上げ。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：切断を固定した混合単体の射は内ホーンへの制限で一致を判定できる。
方針：最初・最後の面への制限の一致を単体の両因子の一致へ移す。
規約：切断は零でも全頂点数でもない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、充填後の指定単体との比較。 -/
lemma join_hom_ext_innerHorn_of_cut {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (hc : (SSet.yonedaEquiv f).1 = (SSet.yonedaEquiv g).1)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 2)
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g := by
  have hfaces (j : Fin (n + 3)) (hj : j ≠ i) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ j).toOrderHom (SSet.yonedaEquiv f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ j).toOrderHom (SSet.yonedaEquiv g) := by
    have he := congrArg (fun q ↦ horn.ι i j hj ≫ q) h
    rw [← Category.assoc, horn.ι_ι, ← Category.assoc, horn.ι_ι] at he
    have hh := congrArg SSet.yonedaEquiv he
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at hh
    exact hh
  apply SSet.yonedaEquiv.injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_extreme_faces _ _ hc hs0 hs1
    (hfaces 0 (ne_of_gt hi0).symm) (hfaces (Fin.last (n + 2)) (ne_of_gt hi1))

/-- 概要：区間への射影を固定した混合単体の射は内ホーンへの制限で決まる。
方針：区間の零の逆像から切断の等式を得て、両端の面による検出を使う。
規約：混合性は最初の射の切断に要求する。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、区間付き対角の内ホーンの持ち上げの一意性。 -/
lemma join_hom_ext_innerHorn_of_interval {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (ht : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 2)
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g := by
  have he := congrArg SSet.yonedaEquiv ht
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at he
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X Y (n + 2) (SSet.yonedaEquiv f)
  have hg := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X Y (n + 2) (SSet.yonedaEquiv g)
  rw [he] at hf
  exact join_hom_ext_innerHorn_of_cut n i hi0 hi1 (Fin.ext (hf.symm.trans hg)) hs0 hs1 h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
