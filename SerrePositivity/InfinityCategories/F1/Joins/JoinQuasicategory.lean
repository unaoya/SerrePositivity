module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinMixedHornFilling
public import SerrePositivity.InfinityCategories.F1.Joins.JoinIntervalEndpointPullbacks
public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagonalInnerFibration
public import SerrePositivity.InfinityCategories.F1.Fibrations.ThinNerveInnerFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の通常の join と相対 join の quasicategory 性。
方針：時間の切断で内ホーンを分け、通常の join への inner fibration で相対 join へ移す。
規約：モデル構造や未証明の比較定理を使わない。
使われ方：Kerodon Proposition 4.3.3.24、Proposition 5.2.3.11、区間上の相対 join の射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの quasicategory の join は quasicategory。
方針：片側に定値な時間では因子のホーンを充填し、混合時間では両端の面を貼る。
規約：空の quasicategory も許す。
使われ方：Kerodon Proposition 4.3.3.24、relative join の全空間の充填性。 -/
@[kerodon 02QV]
instance join_quasicategory (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    Quasicategory (join X Y) where
  hornFilling' n i a hi0 hi1 := by
    obtain ⟨t, ht⟩ := Quasicategory.hornFilling hi0 hi1 (a ≫ joinIntervalProjection X Y)
    by_cases hr : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0
    · have hat : a ≫ joinIntervalProjection X Y =
          SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
        rw [ht, intervalHom_eq_const_one_of_cut_zero t hr, SSet.comp_const]
      obtain ⟨b, hb⟩ := join_exists_factor_inr_of_interval_one a hat
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 b
      refine ⟨c ≫ joinInr X Y, ?_⟩
      rw [← hb, hc, Category.assoc]
    by_cases hl : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 3
    · have hat : a ≫ joinIntervalProjection X Y =
          SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
        rw [ht, intervalHom_eq_const_zero_of_cut_all t hl, SSet.comp_const]
      obtain ⟨b, hb⟩ := join_exists_factor_inl_of_interval_zero a hat
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 b
      refine ⟨c ≫ joinInl X Y, ?_⟩
      rw [← hb, hc, Category.assoc]
    have ht0 : 0 < Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 := by omega
    have ht1 : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2 := by
      have hb := Join.pullCut_le (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
      change Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 3 at hb
      omega
    obtain ⟨l, hl, _⟩ := join_mixed_innerHorn_filling n i hi0 hi1 a t ht.symm ht0 ht1
    exact ⟨l, hl.symm⟩

/-- 概要：quasicategory の図式の relative join は quasicategory。
方針：通常の join への inner fibration と通常の join の quasicategory 性を使う。
規約：二つの構造射は任意の関手。
使われ方：Kerodon Proposition 5.2.3.11、区間上の fibration の全空間。 -/
@[kerodon 024C]
instance relativeJoin_quasicategory {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    Quasicategory (relativeJoin f g) :=
  quasicategory_of_innerFibration (pullback.fst (joinMap f g) (joinDiagonal S))

/-- 概要：quasicategory の relative join の区間への射影は inner fibration。
方針：全空間の quasicategory 性と標準単体への射の内ホーンの一意性を使う。
規約：共通の底への二つの関手は任意。
使われ方：Kerodon Proposition 5.2.3.11、Proposition 5.2.3.15、cocartesian fibration の内ホーン条件。 -/
@[kerodon 024C]
instance relativeJoinProjection_innerFibration {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (relativeJoinProjection f g) :=
  stdSimplexTarget_innerFibration 1 (relativeJoinProjection f g)

end SerrePositivity.InfinityCategories
