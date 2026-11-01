module

public import SerrePositivity.InfinityCategories.F2.Ind.PrecompositionCoconeRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderEquivalence
public import SerrePositivity.InfinityCategories.Kan.PrismEndpointRightAnodyne
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：相対 join の右端への native 全余錐の制限は同値。
方針：円柱への制限同値と円柱の右端への right anodyne な制限を合成する。
規約：元の構造射の単射性や底の quasicategory 性は不要。
使われ方：同じ大域 Kan 族の両端に沿う native 余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 写像円柱の右端包含は任意の構造射について right anodyne。 -/
lemma mappingCylinderInr_rightAnodyne {K C : SSet.{u}} (p : K ⟶ C) :
    rightAnodyneExtensions (pushout.inr (prismEndpoint 1 K) p) :=
  MorphismProperty.of_isPushout (IsPushout.of_hasPushout (prismEndpoint 1 K) p).flip
    (prismEndpoint_one_rightAnodyne K)

/-- 元の相対 join 図式の全余錐空間の右制限は、同じ図式について同値。 -/
lemma relativeJoinInr_nativeRestriction_isQCatEquivalence
    {K C X : SSet.{u}} [Quasicategory X] (p : K ⟶ C)
    (H : relativeJoin p (𝟙 C) ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict H (relativeJoinInr p (𝟙 C))) := by
  let e := relativeJoinCylinderComparison p
  let r := pushout.inr (prismEndpoint 1 K) p
  have : Mono r :=
    Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout (prismEndpoint 1 K) p)
  have ht : TrivialKanFibration (sliceUnderRestrict (e ≫ H) r) :=
    sliceUnderRestrict_trivialKanFibration (e ≫ H) r (mappingCylinderInr_rightAnodyne p)
  have h := (sliceUnderRestrict_isQCatEquivalence_of_precompositionEquivalence H e
    (isPrecompositionEquivalence_relativeJoinCylinderComparison p)).comp
      (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict (e ≫ H) r)).isQCatEquivalence
  change IsQCatEquivalence (sliceUnderRestrict H e ≫ sliceUnderRestrict (e ≫ H) r) at h
  rw [sliceUnderRestrict_comp] at h
  have he : r ≫ e = relativeJoinInr p (𝟙 C) := relativeJoinCylinderComparison_inr p
  exact (congrArg (fun s => IsQCatEquivalence (sliceUnderRestrict H s)) he).mp h

/-- 右端の制限は、指定した元の全余錐の native 余極限性を保ち検出する。 -/
lemma relativeJoin_isColimitCone_iff_restrict_inr
    {K C X : SSet.{u}} [Quasicategory X] (p : K ⟶ C)
    {H : relativeJoin p (𝟙 C) ⟶ X} (c : JoinCocone H) :
    IsColimitCone c ↔ IsColimitCone (c.restrict (relativeJoinInr p (𝟙 C))) :=
  (relativeJoinInr_nativeRestriction_isQCatEquivalence p H).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Ind
