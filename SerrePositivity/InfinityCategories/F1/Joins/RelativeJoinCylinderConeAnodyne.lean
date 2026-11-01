module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderCone
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono
public import SerrePositivity.InfinityCategories.F1.Joins.JoinLeftBoundaryAnodyne
public import SerrePositivity.InfinityCategories.Kan.PrismEndpointRightAnodyne
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor

/-!
概要：mapping cylinder から右錐への比較の inner anodyne 性。
方針：終域の最後の面に沿う円柱を join の相対境界の pushout と同定する。
規約：標準単体の終域を一つ大きくする場合。
使われ方：Kerodon Proposition 5.2.4.5、終域の次元に関する帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の面に沿う終域の変更が誘導する mapping cylinder の射。
方針：円柱部分を保ち、終域部分に最後の面を合成する。
規約：区間の一端を貼る mapping cylinder。
使われ方：Kerodon Proposition 5.2.4.5、二段の pushout の貼り合わせ。 -/
noncomputable def relativeJoinCylinderLastFaceMap {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout (prismEndpoint 1 Δ[m]) f ⟶
      pushout (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) :=
  pushout.desc (pushout.inl _ _)
    (stdSimplex.δ (Fin.last (n + 1)) ≫ pushout.inr _ _) (by
      simpa only [Category.assoc] using
        (pushout.condition (f := prismEndpoint 1 (Δ[m] : SSet.{u}))
          (g := f ≫ stdSimplex.δ (Fin.last (n + 1)))))

/-- 概要：円柱の終域変更の射は右錐の比較を合成すると右錐の左包含になる。
方針：円柱部分と終域部分に制限し、最後の面と右錐の逆同型を打ち消す。
規約：標的は元の mapping cylinder の右錐。
使われ方：Kerodon Proposition 5.2.4.5、相対境界からの射の同定。 -/
lemma relativeJoinCylinderLastFaceMap_cone {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinCylinderLastFaceMap f ≫ relativeJoinCylinderConeMap f =
      joinInl (pushout (prismEndpoint 1 Δ[m]) f) Δ[0] := by
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderLastFaceMap, pushout.inl_desc,
      relativeJoinCylinderConeMap_inl]
  · rw [← Category.assoc, relativeJoinCylinderLastFaceMap, pushout.inr_desc,
      Category.assoc, relativeJoinCylinderConeMap_inr, ← Category.assoc,
      relativeJoinCylinderCone_face_inv, joinInl_joinMap]

/-- 概要：大きい終域の mapping cylinder は元の円柱に終域の右錐を貼った pushout。
方針：二つの円柱の定義の pushout を打ち消し、標準単体の右錐の同型で移す。
規約：共通部分は元の終域 Δ[n]。
使われ方：Kerodon Proposition 5.2.4.5、join の相対境界との同定。 -/
lemma relativeJoinCylinderCone_isPushout {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsPushout (joinInl (Δ[n] : SSet.{u}) Δ[0]) (pushout.inr (prismEndpoint 1 Δ[m]) f)
      ((joinStdSimplexIso n 0).hom ≫
        pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))))
      (relativeJoinCylinderLastFaceMap f) := by
  have hw : pushout.inr (prismEndpoint 1 Δ[m]) f ≫ relativeJoinCylinderLastFaceMap f =
      stdSimplex.δ (Fin.last (n + 1)) ≫
        pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) :=
    pushout.inr_desc _ _ _
  have ht : IsPushout (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1)))
      (pushout.inl (prismEndpoint 1 Δ[m]) f ≫ relativeJoinCylinderLastFaceMap f)
      (pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1)))) := by
    rw [relativeJoinCylinderLastFaceMap, pushout.inl_desc]
    exact IsPushout.of_hasPushout _ _
  have hp := (ht.of_top hw (IsPushout.of_hasPushout (prismEndpoint 1 Δ[m]) f)).flip
  apply hp.of_iso (Iso.refl _) (joinStdSimplexIso n 0).symm (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.id_comp, Iso.symm_hom] using
      relativeJoinCylinderCone_face_inv.{u} n
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- 概要：右錐への比較は join の相対境界の射と同型によって一致する。
方針：円柱の pushout からの標準同型を使い、両因子で射を検査する。
規約：同型の逆射を先に合成した等式。
使われ方：Kerodon Proposition 5.2.4.5、inner anodyne 性の移送。 -/
lemma relativeJoinCylinderCone_boundary_factor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinLeftBoundaryMap (pushout.inr (prismEndpoint 1 Δ[m]) f) Δ[0] =
      (relativeJoinCylinderCone_isPushout f).isoPushout.inv ≫ relativeJoinCylinderConeMap f := by
  apply pushout.hom_ext
  · rw [joinLeftBoundaryMap_join, ← Category.assoc, IsPushout.inl_isoPushout_inv,
      Category.assoc, relativeJoinCylinderConeMap_inr, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  · rw [joinLeftBoundaryMap_left, ← Category.assoc, IsPushout.inr_isoPushout_inv,
      relativeJoinCylinderLastFaceMap_cone]

/-- 概要：mapping cylinder から右錐への標準比較は inner anodyne。
方針：終点包含の pushout が right anodyne であることを join の相対境界の定理に適用する。
規約：終域を最後の面で広げる場合の射。
使われ方：Kerodon Proposition 5.2.4.5、右錐を経由した比較の同値性。 -/
lemma relativeJoinCylinderConeMap_innerAnodyne {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    innerAnodyneExtensions (relativeJoinCylinderConeMap f) := by
  have hi : rightAnodyneExtensions (pushout.inr (prismEndpoint 1 Δ[m]) f) :=
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout (prismEndpoint 1 Δ[m]) f).flip
      (prismEndpoint_one_rightAnodyne Δ[m])
  have : Mono (pushout.inr (prismEndpoint 1 Δ[m]) f) :=
    Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout (prismEndpoint 1 Δ[m]) f)
  have h := joinLeftBoundaryMap_innerAnodyne_of_rightAnodyne
    (pushout.inr (prismEndpoint 1 Δ[m]) f) (Δ[0] : SSet.{u}) hi
  rwa [relativeJoinCylinderCone_boundary_factor,
    innerAnodyneExtensions.cancel_left_of_respectsIso] at h

/-- 概要：小さい終域の円柱比較の同値条件は最後の面で終域を広げても保たれる。
方針：円柱から右錐への inner anodyne 射、join で延長した帰納仮定、右錐の同型を合成する。
規約：帰納仮定は元の比較の前合成の同値条件。
使われ方：Kerodon Proposition 5.2.4.5、f(m)<n の場合の次元の帰納。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_lastFace {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : IsPrecompositionEquivalence (relativeJoinCylinderComparison f)) :
    IsPrecompositionEquivalence
      (relativeJoinCylinderComparison (f ≫ stdSimplex.δ (Fin.last (n + 1)))) := by
  rw [← relativeJoinCylinderConeMap_comparison]
  exact (isPrecompositionEquivalence_of_innerAnodyne _
    (relativeJoinCylinderConeMap_innerAnodyne f)).comp
      ((hf.joinMap_left Δ[0]).comp (isPrecompositionEquivalence_of_iso (relativeJoinConeIso f)))

end SerrePositivity.InfinityCategories
