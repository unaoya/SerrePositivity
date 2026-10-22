module

public import SerrePositivity.InfinityCategories.F1.CoherentPointedRestrictionReflection
public import SerrePositivity.InfinityCategories.F1.NativePointedRestrictionReflection
public import SerrePositivity.InfinityCategories.F1.RepresentablePresheafAllSmallLimits

/-!
概要：全表現可能前層による同じ像の極限性が、元の全錐の極限性を検出する。
方針：像の一点からの制限を元の coslice の制限へ反映し、全頂点の極限判定を適用する。
規約：始域は Cᵒᵖ。共変 Hom の判定には反転を別途明示する。
使われ方：F1-5、HTT 5.1.3.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}

/-- 全表現可能前層で同じ錐の像が極限なら、元の錐が極限。 -/
lemma isLimitCone_of_representablePresheafInfinity (c : JoinCone D)
    (hc : ∀ y : C _⦋0⦌, IsLimitCone (mapJoinCone (representablePresheafInfinity y)
      (JoinCone.ulift.{u, u + 1} c))) : IsLimitCone c := by
  apply (isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mpr
  intro x
  let y : C _⦋0⦌ := SSet.opObjEquiv x
  let g := Over.homMk (U := Over.mk D) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  have hs := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mp
    (hc y) pointSpaceVertex).isQCatEquivalence
  have hp := coherentPointedRestriction_of_nativeCone_isQCatEquivalence c
    (representablePresheafInfinity y) hs
  have hr := relativeRestriction_isQCatEquivalence_of_coherentPointed
    (representablePresheafInfinity y) g hp
  rw [← leftFibrationConeRestriction_eq_overPre] at hr
  have ht := (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)))
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))
    (representableCosliceComparison y) (representableCosliceComparison_projection y)
    (representableCosliceComparison_isPrecompositionEquivalence y) c).mpr hr
  have ht' : IsQCatEquivalence (coneSectionRestriction c x) := by
    have hxy : SSet.opObjEquiv.symm y = x := Equiv.symm_apply_apply _ x
    rw [hxy] at ht
    exact ht
  exact ht'.isSimplicialHomotopyEquivalence

/-- 元の小さい全錐の極限性は、全表現可能前層の同じ像の極限性と同値。 -/
lemma isLimitCone_iff_representablePresheafInfinity (c : JoinCone D) :
    IsLimitCone c ↔ ∀ y : C _⦋0⦌,
      IsLimitCone (mapJoinCone (representablePresheafInfinity y) (JoinCone.ulift.{u, u + 1} c)) :=
  ⟨fun hc y ↦ representablePresheafInfinity_isLimit c hc y,
    isLimitCone_of_representablePresheafInfinity c⟩

end SerrePositivity.InfinityCategories
