module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeUniverseNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.ReindexSliceOver
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：通常の全錐の AsSmall 表示での極限性を、元の宇宙持ち上げた全錐へ比較する。
方針：既存の同じ全錐の値の等式と、添字の実同型による再添字付けを使う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の元の係数前層への復帰。
規約：係数圏の宇宙は変えず、元の全錐と全射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ AsSmall 係数表示での元の全錐の極限性は、元の持ち上げ全錐の同じ像と同値。 -/
lemma isLimitCone_asSmallCoefficient_iff {I C : Type u} [SmallCategory I] [SmallCategory C]
    {P : I ⥤ C} (c : Cone P) {E : SSet.{u + 1}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ E) :
    IsLimitCone (mapJoinCone ((nerveAsSmallIso C).inv ≫ F) (nerveCone (asSmallCone c))) ↔
      IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} (nerveCone c))) := by
  let d := mapJoinCone ((nerveAsSmallIso C).inv ≫ F) (nerveCone (asSmallCone c))
  have hv : (d.reindexIso (nerveAsSmallIso I)).val =
      (mapJoinCone F (JoinCone.ulift.{u, u + 1} (nerveCone c))).val := by
    change joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveAsSmallIso I).hom ≫
      ((nerveCone (asSmallCone c)).val ≫ ((nerveAsSmallIso C).inv ≫ F)) =
      (JoinCone.ulift.{u, u + 1} (nerveCone c)).val ≫ F
    rw [← Category.assoc, uliftNerveCone_asSmall_val]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (isLimitCone_iff_reindexIso d (nerveAsSmallIso I)).trans
    (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
