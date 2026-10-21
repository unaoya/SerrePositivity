module
public import SerrePositivity.InfinityCategories.Derived.LeftFibrationConeUniverse
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetTransportRepresentation
/-!
概要：同じ固定始点 Hom の分類図式の全錐切断制限から、元の dg nerve の極限錐を検出する。
方針：実 coslice の切断判定を同じ pointed 表示と宇宙比較で両方向へ移す。
規約：入力 dg 圏の Small 性は不要。使われ方：実導来出力の有限極限保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
/-- 元の実錐を保持する Hom 試験による極限判定。 -/
lemma dgHomTargetConeRestriction_iff (x : C)
    {K : SSet.{max (u + 1) v}} {d : K ⟶ dgNerve R C} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction
      (sliceUnderProjection (SSet.yonedaEquiv.symm (Simplex.vertex x))) c) ↔
    IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
      (mapJoinCone (dgHomTargetUnderlyingSpaceInfinity R C x)
        (JoinCone.ulift.{max (u + 1) v, max (u + 1) v + 1} c))) :=
  LeftTransportRepresentation.uliftConeRestriction_iff _
    (dgHomTargetTransportRepresentation R C x) c
/-- 元の実錐を保持する Hom 試験による極限判定。 -/
lemma dgNerve_isLimitCone_iff_homTargetPointedRestriction
    {K : SSet.{max (u + 1) v}} {d : K ⟶ dgNerve R C} (c : JoinCone d) :
    IsLimitCone c ↔ ∀ x : C,
      IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
        (mapJoinCone (dgHomTargetUnderlyingSpaceInfinity R C x)
          (JoinCone.ulift.{max (u + 1) v, max (u + 1) v + 1} c))) := by
  constructor
  · intro hc x
    have h := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc
      (Simplex.vertex x)).isQCatEquivalence
    exact (dgHomTargetConeRestriction_iff R C x c).mp h
  · intro h
    apply (isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mpr
    intro a
    obtain ⟨x, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective a
    exact ((dgHomTargetConeRestriction_iff R C x c).mpr (h x)).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories
