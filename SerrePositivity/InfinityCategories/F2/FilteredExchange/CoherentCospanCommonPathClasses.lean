module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonInputs
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelKanPathClass
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalReplacementPathRestriction

/-!
概要：共通の左置換の二つの入力における元の指定 path を、native・Kan の指定類へ戻す。
方針：元の候補の全 path と、元の Kan 比較の全円柱を読み出して同じ指定同型へ比較する。
規約：明示した端点の下で指定値を保持。使われ方：左右比較の底における整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg
local notation "eF" => eqToHom (coherentDiagramTotalVertex_object F)

/-- 元の native 候補での第一置換 path の指定類は元の native な可換同型そのもの。 -/
lemma coherentCospanNativeFirstPathIso_heq :
    HEq ((intervalReplacementPathIso nf).precomp
      (coherentCospanConeNativeComparison F X Y Z C ≫
        pullback.fst (intervalReplacementEndpoint nf) ng))
      (coherentCospanConeNativePathDownIso F X Y Z C) := by
  have hr := intervalReplacementPathIso_precomp_heq_pullback nf ng
    (coherentCospanConeNativeComparison F X Y Z C)
  have hp := intervalPullbackHomotopyPoint_pathIso_heq nf ng _ _
    (coherentCospanConeNativeComparisonHomotopy F X Y Z C)
  have he : functorIsoOfSimplicialHomotopy
      (coherentCospanConeNativeComparisonHomotopy F X Y Z C) =
        coherentCospanConeNativePathDownIso F X Y Z C := by
    apply Iso.ext
    exact coherentCospanConeNativeComparisonHomotopy_hom F X Y Z C
  exact hr.trans (hp.trans (heq_of_eq he))

/-- 元の模型での第一置換 path の指定類は、同じ頂点表示で移した指定 Kan 延長の類。 -/
lemma coherentCospanModelFirstPathIso_heq :
    HEq ((intervalReplacementPathIso f).precomp
      (eF ≫ coherentCospanConeKanComparison F X Y Z C ≫
        pullback.fst (intervalReplacementEndpoint f) g))
      ((functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy
        (coherentCospanConeRelativePathHomotopy F X Y Z C)).val).precomp eF) := by
  have he : intervalReplacementPathIso f =
      functorIsoOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f) := by
    apply Iso.ext
    rfl
  rw [he, ← homotopyIso_precomp]
  have hi := homotopyIso_heq_of_h_eq
    (functorHomotopyPrecomp (intervalReplacementCanonicalPathHomotopy f)
      (eF ≫ coherentCospanConeKanComparison F X Y Z C ≫
        pullback.fst (intervalReplacementEndpoint f) g))
    (functorHomotopyPrecomp (coherentCospanConeKanPathHomotopy F X Y Z C) eF)
    (by apply SSet.hom_ext; intro n; rfl)
  have hk : functorIsoOfSimplicialHomotopy
      (functorHomotopyPrecomp (coherentCospanConeKanPathHomotopy F X Y Z C) eF) =
      (functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy
        (coherentCospanConeRelativePathHomotopy F X Y Z C)).val).precomp eF := by
    rw [homotopyIso_precomp, coherentCospanConeKanPathHomotopy_iso]
  exact hi.trans (heq_of_eq hk)

end SerrePositivity.InfinityCategories.F2
