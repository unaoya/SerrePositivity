module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonRightIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanRightInverseImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanValueImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanValueMaps

/-!
概要：共通の右脚の厳密化補正の底の像を、元の右外脚の値比較へ正規化する。
方針：元の逆厳密化の指定像を元の右脚で制限し、元の頂点表示の逆を後合成する。
規約：両端等式は元の脚の式から明示。使われ方：共通の右脚の全指定像の比較。
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
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "g" => continuousKanReplacement.map cg
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nr" => coherentTotalMapNativeValueDown F Y
  (coherentTransformationTotalMap F Y C.toRight)
local notation "t" => eqToHom (coherentDiagramTotalVertex_object Y)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "e" => coherentTotalNativeKanIso Y Z cg
local notation "R" => cospanRectificationRightIso ng g t v e
local notation "p" => intervalReplacementEndpoint g

/-- 右厳密化の逆補正の底の像は、元の右外脚の値比較の前合成そのものである。 -/
lemma coherentCospanCommonRightCorrectionImage :
    HEq (((FunctorIso.precomp (Iso.symm R) nr).postcomp p).postcomp w)
      ((coherentTotalMapNativeValueDownIso Y Z cg).precomp nr) := by
  have hs := cospanRectificationRightMap_over ng g t v e
  have ht : (t ≫ intervalReplacementSection g) ≫ p = t ≫ g := by
    rw [Category.assoc, intervalReplacementSection_endpoint]
  have hi := cospanRectificationRightIso_inverse_image ng g t v e
  have hp := functorIso_precomp_heq_of_heq e (FunctorIso.postcomp (Iso.symm R) p)
    hs.symm ht.symm hi nr
  have hq := functorIso_postcomp_heq_of_heq (FunctorIso.precomp e nr)
    ((FunctorIso.postcomp (Iso.symm R) p).precomp nr)
    (congrArg (fun k => nr ≫ k) hs.symm) (congrArg (fun k => nr ≫ k) ht.symm) hp w
  have hv := functorIso_precomp_heq_of_heq (coherentTotalMapNativeValueDownIso Y Z cg)
    (FunctorIso.postcomp e w) (coherentTotalNativeKanIso_valueSourceMap Y Z cg).symm
    (coherentTotalNativeKanIso_valueTargetMap Y Z cg).symm
    (coherentTotalNativeKanIso_valueImage Y Z cg) nr
  rw [functorIso_precomp_postcomp]
  exact hq.trans ((heq_of_eq (functorIso_precomp_postcomp e nr w)).trans hv)

end SerrePositivity.InfinityCategories.F2
