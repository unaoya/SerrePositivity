module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：inner fibration の join が inner fibration になることを示す。
方針：純粋な時間では因子で持ち上げ、混合時間では両端の面で充填の像を検出する。
規約：因子や底の quasicategory 性は不要。
使われ方：相対 join の底への射影の充填性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：二つの inner fibration の join は inner fibration。
方針：底の単体の時間を使い、両端の分岐と混合分岐を分ける。
規約：対象に quasicategory 性を要求しない。
使われ方：相対 join の prism への射影の底変換。 -/
@[kerodon 02QU]
instance joinMap_innerFibration {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') [InnerFibration f] [InnerFibration g] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) where
  mem := by
    intro A B k hk
    cases hk with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      let t := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y'
      have ht : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y := by
        dsimp only [t]
        rw [← Category.assoc, ← sq.w, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]
      by_cases hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0
      · have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y' =
            SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_one_of_cut_zero t hr
        have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
            SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
          rw [← ht]
          change _ ≫ (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y') = _
          rw [hb, SSet.comp_const]
        obtain ⟨a', ha'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inr_of_interval_one a ha
        obtain ⟨b', hb'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inr_of_interval_one b hb
        let sq' : CommSq a' (horn (n + 2) i).ι g b' := ⟨by
          apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X' Y')).1
          rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap f g, ← Category.assoc, ha', sq.w,
            Category.assoc, hb']⟩
        have : HasLiftingProperty (horn (n + 2) i).ι g :=
          InnerFibration.mem _ (innerHornInclusions.intro i h0 hn)
        exact CommSq.HasLift.mk' {
          l := sq'.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y
          fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
          fac_right := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
            ← Category.assoc, sq'.fac_right, hb'] }
      by_cases hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 3
      · have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y' =
            SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_zero_of_cut_all t hl
        have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
            SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
          rw [← ht]
          change _ ≫ (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y') = _
          rw [hb, SSet.comp_const]
        obtain ⟨a', ha'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inl_of_interval_zero a ha
        obtain ⟨b', hb'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_exists_factor_inl_of_interval_zero b hb
        let sq' : CommSq a' (horn (n + 2) i).ι f b' := ⟨by
          apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X' Y')).1
          rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap f g, ← Category.assoc, ha', sq.w,
            Category.assoc, hb']⟩
        have : HasLiftingProperty (horn (n + 2) i).ι f :=
          InnerFibration.mem _ (innerHornInclusions.intro i h0 hn)
        exact CommSq.HasLift.mk' {
          l := sq'.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y
          fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
          fac_right := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
            ← Category.assoc, sq'.fac_right, hb'] }
      have ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 :=
        Nat.pos_of_ne_zero hr
      have ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2 := by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
        change _ ≤ n + 3 at h
        omega
      obtain ⟨l, hla, hlt⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_mixed_innerHorn_filling n i h0 hn a t ht ht0 ht1
      refine CommSq.HasLift.mk' { l := l, fac_left := hla, fac_right := ?_ }
      have hw : (horn (n + 2) i).ι ≫ (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) = (horn (n + 2) i).ι ≫ b := by
        rw [← Category.assoc, hla]
        exact sq.w
      have hcut : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
          (SSet.yonedaEquiv b).1.val := by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv
          (SSet.yonedaEquiv (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y'))).toOrderHom 1 = _
        rw [SSet.yonedaEquiv_comp]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X' Y' _ _
      rw [hcut] at ht0 ht1
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_ext_extreme_faces_of_interval (n + 1) (f := b) (g := l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g)
        (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]; exact hlt.symm)
        ht0 ht1 ?_ ?_).symm
      · have h := congrArg (fun z ↦ horn.ι i 0 (ne_of_gt h0).symm ≫ z) hw
        simpa only [← Category.assoc, horn.ι_ι] using h.symm
      · have h := congrArg (fun z ↦ horn.ι i (Fin.last (n + 2)) (ne_of_gt hn) ≫ z) hw
        simpa only [← Category.assoc, horn.ι_ι] using h.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
