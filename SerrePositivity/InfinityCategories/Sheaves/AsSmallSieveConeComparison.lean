module

public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSieveComparison
public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSiteShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeUniverseNaturality

/-!
概要：AsSmall の表示の被覆篩と、元の引き戻し篩の指定制限錐を比較する。
方針：構成済みの篩圏の同値と、通常錐の宇宙表示の自然性を合成する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の小さい模型への層条件の輸送。
規約：頂点だけでなく指定錐の全射を比較し、係数の宇宙を上げない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}
variable (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U))

/-- AsSmall の篩比較の順射は、元の同じ反対関手の nerve である。 -/
lemma asSmallSieveShapeEquivalence_hom :
    (asSmallSieveShapeEquivalence S).hom =
      (asSmallSiteShapeIso (sieveCategory (S.functorPullback AsSmall.up))).hom ≫
        nerveMap (asSmallSieveFunctor S).op := rfl

/-- 元の篩錐を宇宙移送すると、AsSmall の篩錐を同じ関手で制限した錐になる。 -/
lemma asSmallSieveFunctor_cone :
    (asSmallOppositeEquivalence C).functor.mapCone
      (asSmallCone (sieveCone (S.functorPullback AsSmall.up))) =
    (sieveCone S).whisker
      ((asSmallOppositeEquivalence (sieveCategory (S.functorPullback AsSmall.up))).functor ⋙
        (asSmallSieveFunctor S).op) := rfl

/-- 係数と同じ宇宙の AsSmall の制限錐を、元の指定制限錐へ戻す全射の等式。 -/
lemma asSmallRestrictionCone_val {E : SSet.{u + 1}} [Quasicategory E]
    (O : nerve (AsSmall.{u + 1} C)ᵒᵖ ⟶ E) :
    (restrictJoinCone (nativeRestrictionCone O S) (asSmallSieveShapeEquivalence S).hom).val =
      (restrictionCone ((asSmallSiteShapeIso C).hom ≫ O)
        (S.functorPullback AsSmall.up)).val := by
  let A := sieveCategory (S.functorPullback AsSmall.up)
  let c := sieveCone (S.functorPullback AsSmall.up)
  let H := (asSmallOppositeEquivalence A).functor ⋙ (asSmallSieveFunctor S).op
  let q := (asSmallOppositeEquivalence C).functor
  let i := joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveAsSmallIso.{u, u + 1} Aᵒᵖ).hom
  have hc : q.mapCone (asSmallCone c) = (sieveCone S).whisker H :=
    asSmallSieveFunctor_cone S
  have hj : joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      ((nerveAsSmallIso.{u, u + 1} Aᵒᵖ).hom ≫ nerveMap H) =
      i ≫ joinMap (𝟙 _) (nerveMap H) := by
    rw [← joinMap_comp, Category.id_comp]
  calc
    _ = i ≫ (joinMap (𝟙 _) (nerveMap H) ≫ (nerveCone (sieveCone S)).val) ≫ O := by
      change joinMap (𝟙 _) ((nerveAsSmallIso.{u, u + 1} Aᵒᵖ).hom ≫ nerveMap H) ≫
        ((nerveCone (sieveCone S)).val ≫ O) = _
      rw [hj]
      simp only [Category.assoc]
    _ = i ≫ (nerveCone (q.mapCone (asSmallCone c))).val ≫ O := by
      rw [nerveCone_whisker, ← hc]
    _ = (i ≫ (nerveCone (asSmallCone c)).val) ≫ nerveMap q ≫ O := by
      rw [← nerveCone_mapCone]
      simp only [Category.assoc]
    _ = (nerveCone c).ulift.val ≫ (nerveAsSmallIso.{u, u + 1} Cᵒᵖ).hom ≫ nerveMap q ≫ O := by
      rw [uliftNerveCone_asSmall_val]
      simp only [Category.assoc]
    _ = _ := rfl

/-- 同じ元の被覆篩の指定錐について、小さい表示で極限性を保存し反映する。 -/
lemma isLimit_asSmallRestrictionCone_iff {E : SSet.{u + 1}} [Quasicategory E]
    (O : nerve (AsSmall.{u + 1} C)ᵒᵖ ⟶ E) :
    IsLimitCone (restrictionCone ((asSmallSiteShapeIso C).hom ≫ O)
      (S.functorPullback AsSmall.up)) ↔ IsLimitCone (nativeRestrictionCone O S) :=
  (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _
    (asSmallRestrictionCone_val S O)).symm.trans
      (isLimitCone_iff_restrict_equivalentShape (asSmallSieveShapeEquivalence S).hom
        (asSmallSieveShapeEquivalence S).isQCatEquivalence (nativeRestrictionCone O S)).symm

end SerrePositivity.InfinityCategories.Sheaves
