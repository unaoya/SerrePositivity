module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeFirstPathMaps
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalInversePathIsoImage
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq

/-!
概要：左厳密化の逆 path 成分の像を元の native 可換同型の逆へ同定する。
方針：同じ標的同型の往復を相殺し、明示した両端の式の下で元の path の逆を回収する。
規約：元の指定 path を保持。使われ方：共通の左脚の第一因子の像の正規化。
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
local notation "nf" => coherentTotalMapNativeValueDown X Z
  (coherentTransformationTotalMap X Z C.fromLeft)
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "aN" => coherentCospanConeNativeComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint nf) ng
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 元の逆 path 成分の像は元の native な指定可換同型の逆そのものである。 -/
lemma coherentCospanNativeInversePathImage :
    HEq ((FunctorIso.precomp (functorIsoOfEq ((intervalReplacementPathIso nf).postcomp v)
      (Category.assoc (pullback.snd ((intervalEndpointNatTrans 0).app
        (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj) nf) nf v)
        rfl).symm aN).postcomp w)
      (coherentCospanConeNativePathDownIso F X Y Z C).symm := by
  have hp := intervalReplacementInversePathIso_image nf aN
    (eqToIso (coherentDiagramTotalVertex_object Z))
  have hi := functorIso_symm_heq_of_heq (coherentCospanConeNativePathDownIso F X Y Z C)
    ((intervalReplacementPathIso nf).precomp aN)
    (coherentCospanNativeFirstPathSourceMap F X Y Z C).symm
    (coherentCospanNativeFirstPathTargetMap F X Y Z C).symm
    (coherentCospanNativeFirstPathIso_heq F X Y Z C)
  exact hp.trans hi

end SerrePositivity.InfinityCategories.F2
