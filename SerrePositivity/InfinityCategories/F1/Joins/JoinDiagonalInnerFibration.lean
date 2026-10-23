module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoin
public import SerrePositivity.InfinityCategories.F1.Joins.JoinMixedHornDetection
public import SerrePositivity.InfinityCategories.F1.Joins.JoinIntervalEndpointPullbacks
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono

/-!
概要：quasicategory の区間付き対角は inner fibration。
方針：片側だけの単体では既存の係数を復元し、混合単体では係数の内ホーンを充填する。
規約：モデル構造や join 全体の quasicategory 性を仮定しない。
使われ方：Kerodon Lemma 5.2.3.12、相対 join の内ホーンの持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：時間が定値の prism への射は係数への射と端点包含の合成。
方針：第一成分を時間の条件、第二成分を恒等式で比較する。
規約：端点 i は任意。
使われ方：Kerodon Lemma 5.2.3.12、片側の単体に対する対角の持ち上げ。 -/
lemma prism_eq_comp_endpoint_of_fst {A Y : SSet.{u}} (i : Fin 2)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y)
    (ha : a ≫ fst Δ[1] Y = SSet.const (stdSimplex.obj₀Equiv.symm i)) :
    (a ≫ snd Δ[1] Y) ≫ prismEndpoint i Y = a := by
  apply CartesianMonoidalCategory.hom_ext
  · change (a ≫ snd Δ[1] Y) ≫ SSet.const _ = a ≫ fst Δ[1] Y
    rw [ha, SSet.comp_const]
  · rw [Category.assoc, prismEndpoint_snd, Category.comp_id]

/-- 概要：指定された join への射が左因子を経由すれば対角に沿う持ち上げがある。
方針：時間が零に定値であることから元の係数を復元する。
規約：左の射 j や因子 Y に充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12、内ホーンの左端の分岐。 -/
lemma joinDiagonal_hasLift_of_inl {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ join Y Y) (c : B ⟶ Y)
    (hb : c ≫ joinInl Y Y = b) (sq : CommSq a j (joinDiagonal Y) b) : sq.HasLift := by
  have ht := sq.w =≫ joinIntervalProjection Y Y
  rw [Category.assoc, joinDiagonal_joinIntervalProjection, ← hb] at ht
  simp only [Category.assoc, joinIntervalProjection_inl, SSet.comp_const] at ht
  have ha := prism_eq_comp_endpoint_of_fst 0 a ht
  have hac : (a ≫ snd Δ[1] Y) ≫ joinInl Y Y = j ≫ b := by
    calc
      _ = ((a ≫ snd Δ[1] Y) ≫ prismEndpoint 0 Y) ≫ joinDiagonal Y := by
        simp only [Category.assoc, prismEndpoint_zero_joinDiagonal]
      _ = a ≫ joinDiagonal Y := by rw [ha]
      _ = j ≫ b := sq.w
  have hc : a ≫ snd Δ[1] Y = j ≫ c := by
    apply (cancel_mono (joinInl Y Y)).1
    simpa only [Category.assoc, hb] using hac
  refine CommSq.HasLift.mk' { l := c ≫ prismEndpoint 0 Y, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, ← hc, ha]
  · rw [Category.assoc, prismEndpoint_zero_joinDiagonal, hb]

/-- 概要：指定された join への射が右因子を経由すれば対角に沿う持ち上げがある。
方針：時間が一に定値であることから元の係数を復元する。
規約：左の射 j や因子 Y に充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12、内ホーンの右端の分岐。 -/
lemma joinDiagonal_hasLift_of_inr {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ join Y Y) (c : B ⟶ Y)
    (hb : c ≫ joinInr Y Y = b) (sq : CommSq a j (joinDiagonal Y) b) : sq.HasLift := by
  have ht := sq.w =≫ joinIntervalProjection Y Y
  rw [Category.assoc, joinDiagonal_joinIntervalProjection, ← hb] at ht
  simp only [Category.assoc, joinIntervalProjection_inr, SSet.comp_const] at ht
  have ha := prism_eq_comp_endpoint_of_fst 1 a ht
  have hac : (a ≫ snd Δ[1] Y) ≫ joinInr Y Y = j ≫ b := by
    calc
      _ = ((a ≫ snd Δ[1] Y) ≫ prismEndpoint 1 Y) ≫ joinDiagonal Y := by
        simp only [Category.assoc, prismEndpoint_one_joinDiagonal]
      _ = a ≫ joinDiagonal Y := by rw [ha]
      _ = j ≫ b := sq.w
  have hc : a ≫ snd Δ[1] Y = j ≫ c := by
    apply (cancel_mono (joinInr Y Y)).1
    simpa only [Category.assoc, hb] using hac
  refine CommSq.HasLift.mk' { l := c ≫ prismEndpoint 1 Y, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, ← hc, ha]
  · rw [Category.assoc, prismEndpoint_one_joinDiagonal, hb]

/-- 概要：quasicategory の区間付き対角は inner fibration。
方針：片側の切断では係数を指定単体から復元し、混合切断では係数の内ホーンを充填する。
規約：join Y Y の充填性を入力には要求しない。
使われ方：Kerodon Lemma 5.2.3.12、相対 join の quasicategory 性と射影の準備。 -/
instance joinDiagonal_innerFibration (Y : SSet.{u}) [Quasicategory Y] :
    InnerFibration (joinDiagonal Y) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hi0 hi1 =>
      constructor
      intro a b sq
      by_cases hr : (SSet.yonedaEquiv b).1.val = 0
      · obtain ⟨c, hc⟩ := join_hom_exists_factor_inr_of_cut b hr
        exact joinDiagonal_hasLift_of_inr _ a b c hc sq
      by_cases hl : (SSet.yonedaEquiv b).1.val = n + 3
      · obtain ⟨c, hc⟩ := join_hom_exists_factor_inl_of_cut b hl
        exact joinDiagonal_hasLift_of_inl _ a b c hc sq
      have hs0 : 0 < (SSet.yonedaEquiv b).1.val := by omega
      have hs1 : (SSet.yonedaEquiv b).1.val ≤ n + 2 := by
        have hb := (SSet.yonedaEquiv b).1.isLt
        change (SSet.yonedaEquiv b).1.val < n + 4 at hb
        omega
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling hi0 hi1 (a ≫ snd Δ[1] Y)
      let t := b ≫ joinIntervalProjection Y Y
      let l := lift t c
      have ht : a ≫ fst Δ[1] Y = (horn (n + 2) i).ι ≫ t := by
        have he := sq.w =≫ joinIntervalProjection Y Y
        simpa only [Category.assoc, joinDiagonal_joinIntervalProjection] using he
      have ha : (horn (n + 2) i).ι ≫ l = a := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, lift_fst]
          exact ht.symm
        · rw [Category.assoc, lift_snd]
          exact hc.symm
      refine CommSq.HasLift.mk' { l := l, fac_left := ha, fac_right := ?_ }
      apply Eq.symm
      apply join_hom_ext_innerHorn_of_interval n i hi0 hi1
        (f := b) (g := l ≫ joinDiagonal Y) (hs0 := hs0) (hs1 := hs1)
      · rw [Category.assoc, joinDiagonal_joinIntervalProjection]
        exact (lift_fst t c).symm
      · rw [← Category.assoc, ha]
        exact sq.w.symm

/-- 概要：quasicategory を共通の底とする relative join から通常の join への射は inner fibration。
方針：区間付き対角の inner fibration 性を底変換する。
規約：左右の因子の充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.13、相対 join の内ホーンの還元。 -/
instance relativeJoin_fst_innerFibration {X Y S : SSet.{u}} [Quasicategory S]
    (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (pullback.fst (joinMap f g) (joinDiagonal S)) :=
  ⟨innerFibrations.pullback_fst _ _ (InnerFibration.mem (q := joinDiagonal S))⟩

end SerrePositivity.InfinityCategories
