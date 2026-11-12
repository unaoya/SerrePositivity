module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoin
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinMixedHornDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalEndpointPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono

/-!
概要：quasicategory の区間付き対角は inner fibration。
方針：片側だけの単体では既存の係数を復元し、混合単体では係数の内ホーンを充填する。
規約：モデル構造や join 全体の quasicategory 性を仮定しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、相対 join の内ホーンの持ち上げ。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：時間が定値の prism への射は係数への射と端点包含の合成。
方針：第一成分を時間の条件、第二成分を恒等式で比較する。
規約：端点 i は任意。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、片側の単体に対する対角の持ち上げ。 -/
lemma prism_eq_comp_endpoint_of_fst {A Y : SSet.{u}} (i : Fin 2)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y)
    (ha : a ≫ fst Δ[1] Y = SSet.const (stdSimplex.obj₀Equiv.symm i)) :
    (a ≫ snd Δ[1] Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Y = a := by
  apply CartesianMonoidalCategory.hom_ext
  · change (a ≫ snd Δ[1] Y) ≫ SSet.const _ = a ≫ fst Δ[1] Y
    rw [ha, SSet.comp_const]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.comp_id]

/-- 概要：指定された join への射が左因子を経由すれば対角に沿う持ち上げがある。
方針：時間が零に定値であることから元の係数を復元する。
規約：左の射 j や因子 Y に充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの左端の分岐。 -/
lemma joinDiagonal_hasLift_of_inl {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Y Y) (c : B ⟶ Y)
    (hb : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Y Y = b) (sq : CommSq a j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) b) : sq.HasLift := by
  have ht := sq.w =≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection Y Y
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection, ← hb] at ht
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inl, SSet.comp_const] at ht
  have ha := prism_eq_comp_endpoint_of_fst 0 a ht
  have hac : (a ≫ snd Δ[1] Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Y Y = j ≫ b := by
    calc
      _ = ((a ≫ snd Δ[1] Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y := by
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_zero_joinDiagonal]
      _ = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y := by rw [ha]
      _ = j ≫ b := sq.w
  have hc : a ≫ snd Δ[1] Y = j ≫ c := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Y Y)).1
    simpa only [Category.assoc, hb] using hac
  refine CommSq.HasLift.mk' { l := c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Y, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, ← hc, ha]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_zero_joinDiagonal, hb]

/-- 概要：指定された join への射が右因子を経由すれば対角に沿う持ち上げがある。
方針：時間が一に定値であることから元の係数を復元する。
規約：左の射 j や因子 Y に充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの右端の分岐。 -/
lemma joinDiagonal_hasLift_of_inr {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Y Y) (c : B ⟶ Y)
    (hb : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Y Y = b) (sq : CommSq a j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) b) : sq.HasLift := by
  have ht := sq.w =≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection Y Y
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection, ← hb] at ht
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inr, SSet.comp_const] at ht
  have ha := prism_eq_comp_endpoint_of_fst 1 a ht
  have hac : (a ≫ snd Δ[1] Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Y Y = j ≫ b := by
    calc
      _ = ((a ≫ snd Δ[1] Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y := by
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_one_joinDiagonal]
      _ = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y := by rw [ha]
      _ = j ≫ b := sq.w
  have hc : a ≫ snd Δ[1] Y = j ≫ c := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Y Y)).1
    simpa only [Category.assoc, hb] using hac
  refine CommSq.HasLift.mk' { l := c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Y, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, ← hc, ha]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_one_joinDiagonal, hb]

/-- 概要：quasicategory の区間付き対角は inner fibration。
方針：片側の切断では係数を指定単体から復元し、混合切断では係数の内ホーンを充填する。
規約：join Y Y の充填性を入力には要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、相対 join の quasicategory 性と射影の準備。 -/
instance joinDiagonal_innerFibration (Y : SSet.{u}) [Quasicategory Y] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hi0 hi1 =>
      constructor
      intro a b sq
      by_cases hr : (SSet.yonedaEquiv b).1.val = 0
      · obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_hom_exists_factor_inr_of_cut b hr
        exact joinDiagonal_hasLift_of_inr _ a b c hc sq
      by_cases hl : (SSet.yonedaEquiv b).1.val = n + 3
      · obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_hom_exists_factor_inl_of_cut b hl
        exact joinDiagonal_hasLift_of_inl _ a b c hc sq
      have hs0 : 0 < (SSet.yonedaEquiv b).1.val := by omega
      have hs1 : (SSet.yonedaEquiv b).1.val ≤ n + 2 := by
        have hb := (SSet.yonedaEquiv b).1.isLt
        change (SSet.yonedaEquiv b).1.val < n + 4 at hb
        omega
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 (a ≫ snd Δ[1] Y)
      let t := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection Y Y
      let l := lift t c
      have ht : a ≫ fst Δ[1] Y = (horn (n + 2) i).ι ≫ t := by
        have he := sq.w =≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection Y Y
        simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection] using he
      have ha : (horn (n + 2) i).ι ≫ l = a := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, lift_fst]
          exact ht.symm
        · rw [Category.assoc, lift_snd]
          exact hc.symm
      refine CommSq.HasLift.mk' { l := l, fac_left := ha, fac_right := ?_ }
      apply Eq.symm
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_hom_ext_innerHorn_of_interval n i hi0 hi1
        (f := b) (g := l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) (hs0 := hs0) (hs1 := hs1)
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection]
        exact (lift_fst t c).symm
      · rw [← Category.assoc, ha]
        exact sq.w.symm

/-- 概要：quasicategory を共通の底とする relative join から通常の join への射は inner fibration。
方針：区間付き対角の inner fibration 性を底変換する。
規約：左右の因子の充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.13（Tag 02RF）、相対 join の内ホーンの還元。 -/
instance relativeJoin_fst_innerFibration {X Y S : SSet.{u}} [Quasicategory S]
    (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) :=
  ⟨innerFibrations.pullback_fst _ _ (InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
