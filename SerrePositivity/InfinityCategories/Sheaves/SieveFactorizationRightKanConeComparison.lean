module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationRightKanLocalCone

/-!
概要：指定右 Kan 局所錐と、元の局所 comma の制限錐の全射を比較する。
方針：形状比較の三因子と、nerve・AsSmall の全錐の自然性を順に合成する。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の生成系の降下。
規約：元の係数と全脚を保持し、極限性を仮定した比較射を新しく選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C} {E : SSet.{u + 1}}

/-- 元の実形状比較で制限すると、同じ局所 comma の全錐を厳密に回収する。 -/
lemma sieveFactorizationRightKanCone_restrict_val (R S : Sieve U) (t : sieveCategory R)
    (F : Presheaf C E) :
    (restrictJoinCone (sieveFactorizationRightKanTransport R S t F).cone
      (sieveFactorizationRightKanShapeComparison R S t)).val =
        (sieveFactorizationLocalRestrictionCone R S t F).val := by
  let i := (nerveAsSmallIso (sieveFactorizationLocalComma R S t)ᵒᵖ).hom
  let κ := sieveFactorizationRightKanCommaComparison R S t
  let l := (nerveRightKanShapeIso (AsSmall.up.obj (Opposite.op t))
    (sieveFactorizationRightKanFunctor R S)).hom
  let a := (Functor.RightExtension.mk (sieveFactorizationRightKanTarget R)
    (sieveFactorizationRightKanCounit R S)).coneAt (AsSmall.up.obj (Opposite.op t))
  let V := sieveFactorizationRightKanCoefficient F
  have hj : joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (sieveFactorizationRightKanShapeComparison R S t) =
      joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveMap κ) ≫ joinMap (𝟙 (Δ[0] : SSet.{u + 1})) l := by
    rw [sieveFactorizationRightKanShapeComparison_factor]
    change joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (i ≫ nerveMap κ ≫ l) = _
    simp only [← joinMap_comp, Category.id_comp]
  have hl := sieveFactorizationRightKanTransport_local_val R S t F
  change joinMap (𝟙 (Δ[0] : SSet.{u + 1})) l ≫ (sieveFactorizationRightKanTransport R S t F).cone.val =
    (nerveCone a).val ≫ V at hl
  calc
    _ = joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveMap κ) ≫
        (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) l ≫ (sieveFactorizationRightKanTransport R S t F).cone.val)) := by
      change joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (sieveFactorizationRightKanShapeComparison R S t) ≫ _ = _
      rw [hj]
      simp only [Category.assoc]
    _ = joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveMap κ) ≫ ((nerveCone a).val ≫ V)) := by
      rw [hl]
    _ = (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (nerveCone (a.whisker κ)).val) ≫ V := by
      rw [← Category.assoc (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveMap κ)) (nerveCone a).val V,
        nerveCone_whisker]
      exact (Category.assoc _ _ _).symm
    _ = (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (nerveCone (asSmallCone (sieveFactorizationLocalCone R S t))).val) ≫ V := by
      rw [sieveFactorizationRightKanCommaComparison_cone]
    _ = ((nerveCone (sieveFactorizationLocalCone R S t)).ulift.val ≫
        (nerveAsSmallIso Cᵒᵖ).hom) ≫ V := by
      rw [uliftNerveCone_asSmall_val]
    _ = (sieveFactorizationLocalRestrictionCone R S t F).val := by
      change ((_ ≫ (nerveAsSmallIso Cᵒᵖ).hom) ≫ ((nerveAsSmallIso Cᵒᵖ).inv ≫ F)) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rfl

/-- 元の各引き戻し篩での降下と、指定右 Kan 輸送の極限条件は同値。 -/
lemma sieveFactorizationRightKanTransport_isLimit_iff [Quasicategory E]
    (R S : Sieve U) (t : sieveCategory R) (F : Presheaf C E) :
    IsLimitCone (sieveFactorizationRightKanTransport R S t F).cone ↔
      IsLimitCone (restrictionCone F (S.pullback t.obj.hom)) := by
  exact (SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape
    (sieveFactorizationRightKanShapeComparison R S t)
    (sieveFactorizationRightKanShapeComparison_isQCatEquivalence R S t) _).trans
      ((SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _
        (sieveFactorizationRightKanCone_restrict_val R S t F)).trans
          (sieveFactorizationLocalRestrictionCone_isLimit_iff R S t F))

end SerrePositivity.InfinityCategories.Sheaves
