module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafRepresentationRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafOppositeUniverseRightKan
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitMappingComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightKanRestrictionIso
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafAllSmallLimits

/-!
概要：反対前層圏の密度錐を保つ小さい空間値関手の表現同型を構成する。
方針：元の Yoneda 制限から表現対象を作り、二つの右 Kan 延長の全自然同型を得る。
規約：表現対象は元の小さい空間値前層であり、表現同型を入力にしない。
使われ方：presentable 圏の連続前層の表現可能性と随伴関手定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {A : SSet.{u}} [Quasicategory A]

/-- 概要：反対密度錐を保つ小さい空間値関手は元の制限前層によって表現される。
方針：元の全表現可能 Hom と指定宇宙変更後の F を同じ右 Kan 延長として比較する。
規約：全関手の同型を構成し、値ごとの比較へ弱めない。
使われ方：自由前層圏上の表現可能性の存在方向。 -/
def presheafRepresentationIso
    (F : (PresheafInfinity A).op ⟶ SpaceInfinity.{u})
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone F (F1B.coconeReverseCone (presheafDensityCocone P)))) :
    FunctorIso (representablePresheafInfinity (functorVertex (presheafRepresentationCandidate F)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram) := by
  apply rightKanReflRestrictionIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (yonedaInfinityMap A)))
    (presheaf_oppositeDensity_image_isRightKanExtension _ ?_)
    (presheaf_oppositeDensity_image_isRightKanExtension _ ?_)
    (presheafRepresentation_restrictionIso F)
  · intro P
    exact representablePresheafInfinity_isLimit _
      ((F1B.isColimitCone_iff_reverseCone (presheafDensityCocone P)).mp
        (presheafDensityCocone_isColimit P)) _
  · intro P
    rw [mapJoinCone_universe_comp]
    exact spaceUniverseDiagram_map_isLimit _ (hF P)

end SerrePositivity.InfinityCategories.F2.Presentable
