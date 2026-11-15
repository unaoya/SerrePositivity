module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SimplexConeRestriction

public import SerrePositivity.InfinityCategories.Sheaves.TopSieveInitialPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointConeLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointJoinNerveExt
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction

/-!
概要：最大篩の指定制限錐の極限性と、最小位相での前層の層性。
方針：恒等射の点へ制限した錐の全射を計算し、left anodyneな制限から極限性を戻す。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の最大篩の降下。
規約：元の制限錐の頂点と全脚を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 指定した点は元の恒等射の頂点のYoneda表示である。 -/
lemma topSieveInitialPoint_eq (U : 𝒞) : topSieveInitialPoint U = SSet.yonedaEquiv.symm
    (ULift.up (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex
      (Opposite.op (topSieveIdentity U)))) := by
  apply (cancel_mono (SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso
    (sieveCategory (⊤ : Sieve U))ᵒᵖ).hom).mp
  rw [topSieveInitialPoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex] using
    (SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso_vertex
      (sieveCategory (⊤ : Sieve U))ᵒᵖ (Opposite.op (topSieveIdentity U))).symm

/-- 恒等射の点へ制限すると、元の錐は全体として定値になる。 -/
lemma topSieveRestrictionCone_point_val (U : 𝒞) (F : Presheaf 𝒞 E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (restrictionCone F (⊤ : Sieve U))
      (topSieveInitialPoint U)).val =
      SSet.const (F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))) := by
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (sieveCone (⊤ : Sieve U))).ulift
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (topSieveInitialPoint U) ≫ c.val =
      SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso 𝒞ᵒᵖ).hom).mp
    rw [SSet.const_comp]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointJoinNerve_hom_ext
    · apply SSet.yonedaEquiv.injective
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso 𝒞ᵒᵖ).hom.app _ c.vertex = _
      rw [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_vertex]
      rfl
    · apply SSet.yonedaEquiv.injective
      rw [topSieveInitialPoint_eq]
      apply ComposableArrows.ext₀
      rfl
    · rw [topSieveInitialPoint_eq]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (sieveCone (⊤ : Sieve U))).val.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex (Opposite.op (topSieveIdentity U))) ⋙ AsSmall.up = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg]
      refine ComposableArrows.ext₁ rfl rfl ?_
      simp [sieveCone, topSieveIdentity]
      change 𝟙 _ = AsSmall.up.{u, u, u + 1}.map (𝟙 (Opposite.op U))
      simp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (topSieveInitialPoint U) ≫ (c.val ≫ F) = _
  rw [← Category.assoc, hc, SSet.const_comp]

/-- 始対象 (U,id) の脚は恒等射なので、この指定錐が極限錐になる。 -/
lemma topSieveRestrictionCone_isLimit (U : 𝒞) (F : Presheaf 𝒞 E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F (⊤ : Sieve U)) := by
  letI : Mono (topSieveInitialPoint U) := by
    unfold topSieveInitialPoint
    infer_instance
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_leftAnodyne (restrictionCone F (⊤ : Sieve U))
    (topSieveInitialPoint U) (topSieveInitialPoint_leftAnodyne U)).mp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCone_isLimit_of_constant _ _ (topSieveRestrictionCone_point_val U F)


/-- 最小位相では、元の任意の前層が層条件を満たす。 -/
lemma isSheaf_bot (F : Presheaf 𝒞 E) : IsSheaf ⊥ F := by
  intro U S hS
  have hs := GrothendieckTopology.bot_covering.mp hS
  subst S
  exact topSieveRestrictionCone_isLimit U F

end SerrePositivity.InfinityCategories.Sheaves
