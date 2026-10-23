module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteProductPreservation
public import SerrePositivity.InfinityCategories.F1.CoherentPointedRestrictionReflection
public import SerrePositivity.InfinityCategories.F1.NativePointedRestrictionReflection

/-!
概要：前層が元の錐を極限へ送れば、小さい元の全空間の同じ切断制限は同値。
方針：像の一点からの制限を pointed な持ち上げへ戻し、元の小さい全空間へ反映する。
規約：元の全錐と同じ右包含の制限を使う。元の圏の極限存在はここでは主張しない。
使われ方：P_Σ の元の圏における有限余積の構成の、反転した有限積側の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の像が極限であれば、元の小さい全空間の全錐から底への切断制限は同値。 -/
lemma smallLeftConeRestriction_isQCatEquivalence_of_map_isLimit
    {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hc : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c))) :
    IsQCatEquivalence (leftFibrationConeRestriction (smallLeftUnstraighteningProjection F) c) := by
  let g := Over.homMk (U := Over.mk D) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  have hs := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mp
    hc pointSpaceVertex).isQCatEquivalence
  have hp := coherentPointedRestriction_of_nativeCone_isQCatEquivalence c F hs
  have hr := relativeRestriction_isQCatEquivalence_of_coherentPointed F g hp
  rwa [← leftFibrationConeRestriction_eq_overPre] at hr

/-- 有限積を保存する元の前層の全空間は、元の有限積錐の切断制限を同値にする。 -/
lemma smallLeftConeRestriction_isQCatEquivalence_of_finiteProducts
    {B : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hF : PreservesFiniteProductsFromSmallSource F)
    {J : Type u} [Finite J] {D : nerve (Discrete J) ⟶ B}
    (c : JoinCone D) (hc : IsLimitCone c) :
    IsQCatEquivalence (leftFibrationConeRestriction (smallLeftUnstraighteningProjection F) c) :=
  smallLeftConeRestriction_isQCatEquivalence_of_map_isLimit c F (hF.map_isLimit hc)

end SerrePositivity.InfinityCategories.HomotopyLimits
