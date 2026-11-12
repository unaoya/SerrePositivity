module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMixedHornFilling
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalEndpointPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の通常の join と相対 join の quasicategory 性。
方針：時間の切断で内ホーンを分け、通常の join への inner fibration で相対 join へ移す。
規約：モデル構造や未証明の比較定理を使わない。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、Proposition 5.2.3.11（Tag 024C）、区間上の相対 join の射影。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：二つの quasicategory の join は quasicategory。
方針：片側に定値な時間では因子のホーンを充填し、混合時間では両端の面を貼る。
規約：空の quasicategory も許す。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、relative join の全空間の充填性。 -/
@[kerodon 02QV]
instance join_quasicategory (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) where
  hornFilling' n i a hi0 hi1 := by
    obtain ⟨t, ht⟩ := Quasicategory.hornFilling hi0 hi1 (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    by_cases hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0
    · have hat : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
          SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
        rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_one_of_cut_zero t hr, SSet.comp_const]
      obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inr_of_interval_one a hat
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 b
      refine ⟨c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y, ?_⟩
      rw [← hb, hc, Category.assoc]
    by_cases hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 3
    · have hat : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
          SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
        rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_zero_of_cut_all t hl, SSet.comp_const]
      obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inl_of_interval_zero a hat
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 b
      refine ⟨c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y, ?_⟩
      rw [← hb, hc, Category.assoc]
    have ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 := by omega
    have ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2 := by
      have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 3 at hb
      omega
    obtain ⟨l, hl, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_mixed_innerHorn_filling n i hi0 hi1 a t ht.symm ht0 ht1
    exact ⟨l, hl.symm⟩

/-- 概要：quasicategory の図式の relative join は quasicategory。
方針：通常の join への inner fibration と通常の join の quasicategory 性を使う。
規約：二つの構造射は任意の関手。
使われ方：Kerodon Proposition 5.2.3.11（Tag 024C）、区間上の fibration の全空間。 -/
@[kerodon 024C]
instance relativeJoin_quasicategory {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g) :=
  quasicategory_of_innerFibration (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))

/-- 概要：quasicategory の relative join の区間への射影は inner fibration。
方針：全空間の quasicategory 性と標準単体への射の内ホーンの一意性を使う。
規約：共通の底への二つの関手は任意。
使われ方：Kerodon Proposition 5.2.3.11（Tag 024C）、Proposition 5.2.3.15（Tag 024J）、cocartesian fibration の内ホーン条件。 -/
@[kerodon 024C]
instance relativeJoinProjection_innerFibration {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.stdSimplexTarget_innerFibration 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
