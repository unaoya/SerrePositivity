module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinQuasicategory
public import SerrePositivity.InfinityCategories.F1.Fibrations.BaseChange

/-!
概要：inner fibration の join が inner fibration になることを示す。
方針：純粋な時間では因子で持ち上げ、混合時間では両端の面で充填の像を検出する。
規約：因子や底の quasicategory 性は不要。
使われ方：相対 join の底への射影の充填性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの inner fibration の join は inner fibration。
方針：底の単体の時間を使い、両端の分岐と混合分岐を分ける。
規約：対象に quasicategory 性を要求しない。
使われ方：相対 join の prism への射影の底変換。 -/
instance kanJoinMap_innerFibration {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') [InnerFibration f] [InnerFibration g] :
    InnerFibration (joinMap f g) where
  mem := by
    intro A B k hk
    cases hk with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      let t := b ≫ joinIntervalProjection X' Y'
      have ht : (horn (n + 2) i).ι ≫ t = a ≫ joinIntervalProjection X Y := by
        dsimp only [t]
        rw [← Category.assoc, ← sq.w, Category.assoc, joinIntervalProjection_naturality]
      by_cases hr : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0
      · have hb : b ≫ joinIntervalProjection X' Y' =
            SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
          intervalHom_eq_const_one_of_cut_zero t hr
        have ha : a ≫ joinIntervalProjection X Y =
            SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
          rw [← ht]
          change _ ≫ (b ≫ joinIntervalProjection X' Y') = _
          rw [hb, SSet.comp_const]
        obtain ⟨a', ha'⟩ := join_exists_factor_inr_of_interval_one a ha
        obtain ⟨b', hb'⟩ := join_exists_factor_inr_of_interval_one b hb
        let sq' : CommSq a' (horn (n + 2) i).ι g b' := ⟨by
          apply (cancel_mono (joinInr X' Y')).1
          rw [Category.assoc, ← joinInr_joinMap f g, ← Category.assoc, ha', sq.w,
            Category.assoc, hb']⟩
        have : HasLiftingProperty (horn (n + 2) i).ι g :=
          InnerFibration.mem _ (innerHornInclusions.intro i h0 hn)
        exact CommSq.HasLift.mk' {
          l := sq'.lift ≫ joinInr X Y
          fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
          fac_right := by rw [Category.assoc, joinInr_joinMap,
            ← Category.assoc, sq'.fac_right, hb'] }
      by_cases hl : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 3
      · have hb : b ≫ joinIntervalProjection X' Y' =
            SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
          intervalHom_eq_const_zero_of_cut_all t hl
        have ha : a ≫ joinIntervalProjection X Y =
            SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
          rw [← ht]
          change _ ≫ (b ≫ joinIntervalProjection X' Y') = _
          rw [hb, SSet.comp_const]
        obtain ⟨a', ha'⟩ := join_exists_factor_inl_of_interval_zero a ha
        obtain ⟨b', hb'⟩ := join_exists_factor_inl_of_interval_zero b hb
        let sq' : CommSq a' (horn (n + 2) i).ι f b' := ⟨by
          apply (cancel_mono (joinInl X' Y')).1
          rw [Category.assoc, ← joinInl_joinMap f g, ← Category.assoc, ha', sq.w,
            Category.assoc, hb']⟩
        have : HasLiftingProperty (horn (n + 2) i).ι f :=
          InnerFibration.mem _ (innerHornInclusions.intro i h0 hn)
        exact CommSq.HasLift.mk' {
          l := sq'.lift ≫ joinInl X Y
          fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
          fac_right := by rw [Category.assoc, joinInl_joinMap,
            ← Category.assoc, sq'.fac_right, hb'] }
      have ht0 : 0 < Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 :=
        Nat.pos_of_ne_zero hr
      have ht1 : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2 := by
        have h := Join.pullCut_le (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
        change _ ≤ n + 3 at h
        omega
      obtain ⟨l, hla, hlt⟩ := join_mixed_innerHorn_filling n i h0 hn a t ht ht0 ht1
      refine CommSq.HasLift.mk' { l := l, fac_left := hla, fac_right := ?_ }
      have hw : (horn (n + 2) i).ι ≫ (l ≫ joinMap f g) = (horn (n + 2) i).ι ≫ b := by
        rw [← Category.assoc, hla]
        exact sq.w
      have hcut : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
          (SSet.yonedaEquiv b).1.val := by
        change Join.pullCut (stdSimplex.objEquiv
          (SSet.yonedaEquiv (b ≫ joinIntervalProjection X' Y'))).toOrderHom 1 = _
        rw [SSet.yonedaEquiv_comp]
        exact joinIntervalProjection_app_cut X' Y' _ _
      rw [hcut] at ht0 ht1
      apply (join_hom_ext_extreme_faces_of_interval (n + 1) (f := b) (g := l ≫ joinMap f g)
        (by rw [Category.assoc, joinIntervalProjection_naturality]; exact hlt.symm)
        ht0 ht1 ?_ ?_).symm
      · have h := congrArg (fun z ↦ horn.ι i 0 (ne_of_gt h0).symm ≫ z) hw
        simpa only [← Category.assoc, horn.ι_ι] using h.symm
      · have h := congrArg (fun z ↦ horn.ι i (Fin.last (n + 2)) (ne_of_gt hn) ≫ z) hw
        simpa only [← Category.assoc, horn.ι_ι] using h.symm

end SerrePositivity.InfinityCategories
