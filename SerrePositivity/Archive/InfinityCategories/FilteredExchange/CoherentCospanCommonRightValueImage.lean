module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonRightIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanPostImage
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPostcompReduction

/-!
概要：共通の右脚の値比較成分の底の像を、元の右内脚の値比較へ正規化する。
方針：元の端点補正を保持して二段の後合成を行い、切断・終点評価を元の外脚へ戻す。
規約：指定値を保持。使われ方：共通の右脚の全指定像を小宇宙の可換式へ合わせる。
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
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "g" => continuousKanReplacement.map cg
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 同じ右内脚の値比較成分の像は、元の小宇宙の値比較の元の外脚による後合成。 -/
lemma coherentCospanCommonRightValueImage :
    HEq (((functorIsoOfEq ((coherentTotalNativeKanIso F Y cr).postcomp
      (intervalReplacementSection g)) (Category.assoc _ _ _) (Category.assoc _ _ _)).postcomp
        (intervalReplacementEndpoint g)).postcomp w)
      ((coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg)) := by
  let E := coherentTotalNativeKanIso F Y cr
  let e := E.postcomp (intervalReplacementSection g)
  let b := functorIsoOfEq e (Category.assoc _ _ _) (Category.assoc _ _ _)
  have hc : HEq b e := functorIsoOfEq_heq _ _ _
  have hb := functorIso_postcomp_postcomp_heq_of_heq e b
    (Category.assoc _ _ _) (Category.assoc _ _ _) hc (intervalReplacementEndpoint g) w
  have hp := functorIso_postcomp_pair_heq_of_comp_eq E (intervalReplacementSection g)
    (intervalReplacementEndpoint g) g (intervalReplacementSection_endpoint g) w
  exact hb.trans (hp.trans (coherentTotalNativeKanIso_postValueImage F Y Z cr cg))

end SerrePositivity.InfinityCategories.F2
