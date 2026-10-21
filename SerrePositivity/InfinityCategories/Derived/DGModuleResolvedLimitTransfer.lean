module
public import SerrePositivity.InfinityCategories.Derived.DGHomConeLimitCriterion
public import SerrePositivity.InfinityCategories.Derived.ConeHomTestUniverse
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedHomTargetComparison
public import SerrePositivity.InfinityCategories.F2.SquareConePostcomp
/-!
概要：生の dg 入力像の実極限錐を、同じ実半自由出力分解の極限錐へ移す。
方針：元の表現可能 Hom の全関手同型を、同じ全錐の切断制限の判定へ接続する。
規約：生の出力の射影性・入力の Small 性は不要。使われ方：一般 kernel の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実錐の全 Hom 試験による分解後の極限性。 -/
lemma dgModuleResolvedInfinity_isLimitCone_of_raw
    {K : SSet.{max (u + 1) v}} {d : K ⟶ dgNerve R C} (c : JoinCone d)
    (hc : IsLimitCone (mapJoinCone (dgNerve.map F) c)) :
    IsLimitCone (mapJoinCone (dgModuleResolvedInfinity R C E F) c) := by
  apply (dgNerve_isLimitCone_iff_homTargetPointedRestriction R (SemifreeDGModules R E) _).mpr
  intro T
  have hraw := (dgNerve_isLimitCone_iff_homTargetPointedRestriction R (RightModule R E) _).mp hc
    T.val
  have hraw' := (leftFibrationConeRestriction_ulift_postcomp_iff pointedSpaceProjection
    (dgNerve.map F) (dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T.val) c).mp hraw
  have he := leftFibrationConeRestriction_mapJoinCone_iff_of_functorIso pointedSpaceProjection
    (dgModuleResolvedRepresentableHomSpaceIso R C E F T)
    (JoinCone.ulift.{max (u + 1) v, max (u + 1) v + 1} c)
  exact (leftFibrationConeRestriction_ulift_postcomp_iff pointedSpaceProjection
    (dgModuleResolvedInfinity R C E F)
    (dgHomTargetUnderlyingSpaceInfinity R (SemifreeDGModules R E) T) c).mpr (he.mpr hraw')
/-- 同じ実錐の全 Hom 試験による分解後の極限性。 -/
lemma dgModuleResolvedInfinity_isPullbackSquare_of_raw
    (s : (Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1] ⟶ dgNerve R C)
    (hs : IsPullbackSquare (s ≫ dgNerve.map F)) :
    IsPullbackSquare (s ≫ dgModuleResolvedInfinity R C E F) := by
  apply (F2.isLimitCone_map_pullbackCone_iff _ s).mp
  exact dgModuleResolvedInfinity_isLimitCone_of_raw R C E F (pullbackCone s)
    ((F2.isLimitCone_map_pullbackCone_iff _ s).mpr hs)
end SerrePositivity.InfinityCategories
