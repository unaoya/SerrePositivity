module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanPostImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPostcompReduction

/-!
概要：共通の左脚の中央の値比較成分の像を元の小さい値比較の後合成へ戻す。
方針：同じ定値切断と終点評価を元の左外射へ簡約し、元の Kan 値比較の像を回収する。
規約：元の指定値を保持。使われ方：左脚の三因子の指定像の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "f" => continuousKanReplacement.map cf
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 左内脚の同じ値比較成分の像は、元の具体的な左外射による後合成に一致する。 -/
lemma coherentCospanCommonLeftValueImage :
    HEq ((((coherentTotalNativeKanIso F X cl).postcomp (intervalReplacementSection f)).postcomp
      (intervalReplacementEndpoint f)).postcomp w)
      ((coherentTotalMapNativeValueDownIso F X cl).postcomp (coherentTotalVertexMap X Z cf)) := by
  have hp := functorIso_postcomp_pair_heq_of_comp_eq (coherentTotalNativeKanIso F X cl)
    (intervalReplacementSection f) (intervalReplacementEndpoint f) f
    (intervalReplacementSection_endpoint f) w
  exact hp.trans (coherentTotalNativeKanIso_postValueImage F X Z cl cf)

end SerrePositivity.InfinityCategories.F2
