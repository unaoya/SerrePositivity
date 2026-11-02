module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceJoinCofinality
public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：展開した join の右包含が right cofinal なら、coslice の終域射影は余極限を保ち反映する。
方針：反復 coslice の同型と同じ右因子への全制限を照合し、始対象を同値で移す。
規約：元の指定余錐を保存し、別の余錐を存在仮定として追加しない。
使われ方：固定始域の閉包内射圏の余極限閉性の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 展開した図式の右因子へ制限し、元の終域図式の coslice と同一視する。 -/
def uncurriedSourceRightRestriction {K L C : SSet.{u}} {p : K ⟶ C}
    (D : L ⟶ sliceUnder p) :
    sliceUnder (sliceUnderUncurry D) ⟶ sliceUnder (D ≫ sliceUnderProjection p) :=
  sliceUnderRestrict (sliceUnderUncurry D) (joinInr K L) ≫
    eqToHom (congrArg sliceUnder (sliceUnderUncurry_projection D))

/-- 同じ右因子への全制限は、元の余錐の終域への後合成そのもの。 -/
lemma iteratedSliceUnderIso_sourceRightRestriction {K L C : SSet.{u}} {p : K ⟶ C}
    (D : L ⟶ sliceUnder p) :
    (iteratedSliceUnderIso D).hom ≫ uncurriedSourceRightRestriction D =
      sliceUnderPostcomp D (sliceUnderProjection p) := by
  apply sliceUnderUncurry_injective (D ≫ sliceUnderProjection p)
  rw [uncurriedSourceRightRestriction, ← Category.assoc,
    sliceUnderUncurry_eqToHom, sliceUnderUncurry_restrict]
  change joinMap (joinInr K L) (𝟙 (sliceUnder D)) ≫
    sliceUnderUncurry (iteratedSliceUnderForwardFamily D (𝟙 (sliceUnder D))) = _
  rw [iteratedSliceUnderForwardFamily_uncurry,
    ← Category.assoc, joinAssociator_rightPair, sliceUnderUncurry_projection]
  exact (sliceUnderUncurry_postcomp (𝟙 (sliceUnder D)) (sliceUnderProjection p)).symm
  exact sliceUnderUncurry_projection D

/-- join の右包含が cofinal なら、同じ指定余錐の普遍性は終域で判定できる。 -/
lemma sourceCoslice_isColimitCone_iff_projection {K L C : SSet.{u}}
    [Quasicategory K] [Quasicategory L] [Quasicategory C]
    (p : K ⟶ C) (D : L ⟶ sliceUnder p)
    (hr : IsRightCofinal (joinInr K L)) (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (sliceUnderProjection p) c) := by
  have hR : IsQCatEquivalence (uncurriedSourceRightRestriction D) :=
    (Ind.sliceUnderRestrict_equivalence_of_rightCofinal (joinInr K L) hr
      (sliceUnderUncurry D)).comp (qCatEquivalenceOfIso
        (eqToIso (congrArg sliceUnder (sliceUnderUncurry_projection D)))).isQCatEquivalence
  have h := (qCatEquivalenceOfIso (iteratedSliceUnderIso D)).isQCatEquivalence.comp hR
  change IsQCatEquivalence ((iteratedSliceUnderIso D).hom ≫ uncurriedSourceRightRestriction D)
    at h
  rw [iteratedSliceUnderIso_sourceRightRestriction] at h
  exact h.choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
