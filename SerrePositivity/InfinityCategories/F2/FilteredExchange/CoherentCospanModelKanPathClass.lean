module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelKanPathHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanHomotopyExtensionClass
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.HomotopyIsoRawComparison

/-!
概要：元の模型 Kan 比較の指定 path は、元の底固定円柱の指定 Kan 延長の類に一致する。
方針：単位上の全円柱の一致を忠実性で反映し、元の path 制限の端点表示を戻す。
規約：指定同型そのものを比較。使われ方：native 比較候補への弱同値性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "H" => coherentCospanConeRelativePathHomotopy F X Y Z C
local notation "K" => coherentCospanConeKanPathHomotopy F X Y Z C
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight)
local notation "m" => coherentCospanConeKanComparison F X Y Z C

/-- 元の Kan 比較の円柱は、元の底固定円柱の指定 Kan 延長と同じ指定同型を与える。 -/
lemma coherentCospanConeKanPathHomotopy_iso :
    functorIsoOfSimplicialHomotopy K =
      functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy H).val :=
  kanHomotopyExtension_iso_eq H H K (specifiedContinuousKanHomotopy H).val
    (coherentCospanConeKanPathHomotopy_unit F X Y Z C)
    (specifiedContinuousKanHomotopy H).property rfl

/-- 元の Kan 引き戻し path の制限も、明示した二脚の表示の下で同じ指定類である。 -/
lemma coherentCospanConeKanComparison_path_iso_heq :
    HEq ((intervalPullbackPathIso f g).precomp m)
      (functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy H).val) := by
  have he : intervalPullbackPathIso f g =
      functorIsoOfSimplicialHomotopy (intervalPullbackPathHomotopy f g) := by
    apply Iso.ext
    rfl
  rw [he, ← homotopyIso_precomp]
  have hi := homotopyIso_heq_of_h_eq
    (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m) K rfl
  rw [coherentCospanConeKanPathHomotopy_iso] at hi
  exact hi

end SerrePositivity.InfinityCategories.F2
