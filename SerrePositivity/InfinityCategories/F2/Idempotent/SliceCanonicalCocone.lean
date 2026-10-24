module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftIdentityLeg
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal

/-!
概要：元の各点上の全 slice の標準余錐は、任意の関手の後でも余極限。
方針：元の恒等錐の終対象性で一点へ制限し、元の恒等脚を持つ定値余錐を回収する。
規約：元の全余錐と指定頂点を保持する。
使われ方：HTT 5.1.4.7 の全関手の標準左 Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の点上の全 slice の普遍余錐に元の関手を後合成した標準余錐。 -/
def sliceCanonicalCocone {C D : SSet.{u}} (F : C ⟶ D) (c : C _⦋0⦌) :
    JoinCocone (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ F) :=
  ⟨sliceOverUncurry (𝟙 (sliceOver (SSet.yonedaEquiv.symm c))) ≫ F, by
    rw [← Category.assoc, sliceOverUncurry_projection]
    rfl⟩

/-- 元の標準 slice 余錐の恒等点での制限は、同じ値の恒等脚を持つ定値余錐。 -/
lemma sliceCanonicalCocone_identity_restrict {C D : SSet.{u}} (F : C ⟶ D)
    (c : C _⦋0⦌) :
    joinMap (SSet.yonedaEquiv.symm (sliceIdentityCone c)) (𝟙 (Δ[0] : SSet.{u})) ≫
      (sliceCanonicalCocone F c).val = SSet.const (F.app (Opposite.op ⦋0⦌) c) := by
  change joinMap _ _ ≫ (sliceOverUncurry _ ≫ F) = _
  rw [← Category.assoc, ← sliceOverUncurry_precomp, Category.comp_id,
    sliceOverUncurry_yoneda]
  exact SSet.const_comp c F

/-- 元の全 slice の同じ標準余錐は、任意の関手の後でも余極限。 -/
lemma sliceCanonicalCocone_isColimit {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (F : C ⟶ D) (c : C _⦋0⦌) :
    IsColimitCone (sliceCanonicalCocone F c) := by
  have := cofinalPointInclusion_mono (sliceIdentityCone c)
  apply (isColimitCone_iff_restrict_of_rightAnodyne _
    (SSet.yonedaEquiv.symm (sliceIdentityCone c))
    (SerrePositivity.InfinityCategories.F1B.terminalPoint_rightAnodyne (SerrePositivity.InfinityCategories.F1B.sliceIdentityCone_isTerminalVertex c))).2
  apply isColimitCone_of_point_constant _ (F.app (Opposite.op ⦋0⦌) c)
  exact sliceCanonicalCocone_identity_restrict F c

end SerrePositivity.InfinityCategories.F2.Idempotent
