module

public import SerrePositivity.InfinityCategories.F1B.KanJoinMixedInitialHorn
public import SerrePositivity.InfinityCategories.F1B.KanJoinMapInnerFibration

/-!
概要：右恒等の joinMap に関する cocartesian 辺を構成する。
方針：純粋な左辺では元の射の充填を使い、右辺と混合辺では係数から充填する。
規約：右因子や底の quasicategory 性は不要。
使われ方：相対 join の両端の辺による底上の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：左因子に入るとき cocartesian な辺は右恒等の joinMap に関して cocartesian。
方針：時間の切断で外ホーンを分け、混合分岐では係数の持ち上げを使う。
規約：左因子に入らない辺に追加条件はない。
使われ方：左包含の辺の保存と右包含の辺の cocartesian 性。 -/
lemma kanJoinMap_right_id_isCocartesianEdge {X X' Y : SSet.{u}} (f : X ⟶ X')
    (e : (join X Y) _⦋1⦌)
    (he : ∀ s : X _⦋1⦌, (joinInl X Y).app (Opposite.op ⦋1⦌) s = e →
      IsCocartesianEdge f s) : IsCocartesianEdge (joinMap f (𝟙 Y)) e := by
  intro n a b ha sq
  let t := b ≫ joinIntervalProjection X' Y
  have ht : (horn (n + 2) 0).ι ≫ t = a ≫ joinIntervalProjection X Y := by
    dsimp only [t]
    rw [← Category.assoc, ← sq.w, Category.assoc, joinIntervalProjection_naturality]
  by_cases hr : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0
  · have hb : b ≫ joinIntervalProjection X' Y =
        SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      intervalHom_eq_const_one_of_cut_zero t hr
    have hat : a ≫ joinIntervalProjection X Y =
        SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      rw [← ht]
      change _ ≫ (b ≫ joinIntervalProjection X' Y) = _
      rw [hb, SSet.comp_const]
    obtain ⟨a', ha'⟩ := join_exists_factor_inr_of_interval_one a hat
    obtain ⟨b', hb'⟩ := join_exists_factor_inr_of_interval_one b hb
    let sq' : CommSq a' (horn (n + 2) 0).ι (𝟙 Y) b' := ⟨by
      apply (cancel_mono (joinInr X' Y)).1
      rw [Category.assoc, ← joinInr_joinMap f (𝟙 Y), ← Category.assoc, ha', sq.w,
        Category.assoc, hb']⟩
    exact CommSq.HasLift.mk' {
      l := sq'.lift ≫ joinInr X Y
      fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
      fac_right := by rw [Category.assoc, joinInr_joinMap,
        ← Category.assoc, sq'.fac_right, hb'] }
  by_cases hl : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 3
  · have hb : b ≫ joinIntervalProjection X' Y =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      intervalHom_eq_const_zero_of_cut_all t hl
    have hat : a ≫ joinIntervalProjection X Y =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      rw [← ht]
      change _ ≫ (b ≫ joinIntervalProjection X' Y) = _
      rw [hb, SSet.comp_const]
    obtain ⟨a', ha'⟩ := join_exists_factor_inl_of_interval_zero a hat
    obtain ⟨b', hb'⟩ := join_exists_factor_inl_of_interval_zero b hb
    let sq' : CommSq a' (horn (n + 2) 0).ι f b' := ⟨by
      apply (cancel_mono (joinInl X' Y)).1
      rw [Category.assoc, ← joinInl_joinMap f (𝟙 Y), ← Category.assoc, ha', sq.w,
        Category.assoc, hb']⟩
    have hval : (joinInl X Y).app (Opposite.op ⦋1⦌)
        (a'.app (Opposite.op ⦋1⦌) (initialHornEdge n)) = e := by
      have h := congrArg (fun z ↦ z.app (Opposite.op ⦋1⦌) (initialHornEdge n)) ha'
      exact h.trans ha
    have := he _ hval n a' b' rfl sq'
    exact CommSq.HasLift.mk' {
      l := sq'.lift ≫ joinInl X Y
      fac_left := by rw [← Category.assoc, sq'.fac_left, ha']
      fac_right := by rw [Category.assoc, joinInl_joinMap,
        ← Category.assoc, sq'.fac_right, hb'] }
  have hb0 : 0 < (SSet.yonedaEquiv b).1.val := by
    have hc : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
        (SSet.yonedaEquiv b).1.val := by
      rw [SSet.yonedaEquiv_comp, joinIntervalProjection_app_cut]
    rw [hc] at hr
    omega
  have hb1 : (SSet.yonedaEquiv b).1.val ≤ n + 2 := by
    have hc : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
        (SSet.yonedaEquiv b).1.val := by
      rw [SSet.yonedaEquiv_comp, joinIntervalProjection_app_cut]
    rw [hc] at hl
    have h := (SSet.yonedaEquiv b).1.isLt
    change (SSet.yonedaEquiv b).1.val < n + 4 at h
    omega
  obtain ⟨l, hla, hlb⟩ := kanJoinMap_right_id_initialHorn_hasLift_of_mixed n f a b sq.w.symm hb0 hb1
  exact CommSq.HasLift.mk' { l := l, fac_left := hla, fac_right := hlb }

/-- 概要：左包含は元の射の cocartesian 辺を右恒等の joinMap の cocartesian 辺へ送る。
方針：左包含の単射性で元の辺を回収する。
規約：右因子の充填性は不要。
使われ方：相対 join の左端の輸送。 -/
lemma kanJoinMap_right_id_inl_isCocartesianEdge {X X' Y : SSet.{u}}
    (f : X ⟶ X') (s : X _⦋1⦌) (hs : IsCocartesianEdge f s) :
    IsCocartesianEdge (joinMap f (𝟙 Y)) ((joinInl X Y).app (Opposite.op ⦋1⦌) s) := by
  apply kanJoinMap_right_id_isCocartesianEdge
  intro t ht
  have he := (mono_iff_injective ((joinInl X Y).app (Opposite.op ⦋1⦌))).1
    (inferInstance : Mono _) ht
  subst t
  exact hs

/-- 概要：右包含のすべての辺は右恒等の joinMap に関して cocartesian。
方針：左包含から同じ辺が来る可能性を切断の違いで排除する。
規約：右因子の辺の可逆性は不要。
使われ方：相対 join の右端の底上の輸送。 -/
lemma kanJoinMap_right_id_inr_isCocartesianEdge {X X' Y : SSet.{u}}
    (f : X ⟶ X') (s : Y _⦋1⦌) :
    IsCocartesianEdge (joinMap f (𝟙 Y)) ((joinInr X Y).app (Opposite.op ⦋1⦌) s) := by
  apply kanJoinMap_right_id_isCocartesianEdge
  intro t ht
  have hc := congrArg (fun z : Join.Simplex X Y 1 ↦ z.1.val) ht
  change 2 = 0 at hc
  omega

end SerrePositivity.InfinityCategories.F1B
