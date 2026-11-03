module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonRightImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativePathWhiskerComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPostcompFaithful
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.StrictPullbackIsoGluing

/-!
概要：共通の引き戻しへの二比較の左右の指定同型は、底で同じ指定像を持つ。
方針：元の値の指定正方形で両像を揃え、頂点表示の逆の後合成の忠実性で反映する。
規約：両端は元の引き戻し条件で明示。使われ方：引き戻し全体への同型の貼り合わせ。
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
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "p" => intervalReplacementEndpoint (continuousKanReplacement.map cf)
local notation "q" => intervalReplacementEndpoint (continuousKanReplacement.map cg)
local notation "nl" => coherentTotalMapNativeValueDown F X cl
local notation "nr" => coherentTotalMapNativeValueDown F Y cr
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 共通の引き戻しの底で、左右の指定脚比較は同じ指定値を持つ。 -/
lemma coherentCospanCommonBaseCompatibility :
    HEq ((coherentCospanCommonLeftIso F X Y Z C).postcomp p)
      ((coherentCospanCommonRightIso F X Y Z C).postcomp q) := by
  let n := coherentCospanConeNativePathDownIso F X Y Z C
  let a := (coherentTotalMapNativeValueDownIso X Z cf).precomp nl
  let b := (coherentTotalMapNativeValueDownIso F X cl).postcomp (coherentTotalVertexMap X Z cf)
  let c := coherentCospanConeValuePathIso F X Y Z C
  let d := (coherentTotalMapNativeValueDownIso Y Z cg).precomp nr
  let e := (coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg)
  have hs : (n.symm ≪≫ a) ≪≫ b ≪≫ c = d ≪≫ e := by
    exact functorIso_cancel_inverse_prefix n a b c d e
      (coherentCospanConeNativePathDownIso_whisker F X Y Z C)
  have hl := coherentCospanCommonLeftImage F X Y Z C
  have hr := coherentCospanCommonRightImage F X Y Z C
  have hh : HEq (((coherentCospanCommonLeftIso F X Y Z C).postcomp p).postcomp w)
      (((coherentCospanCommonRightIso F X Y Z C).postcomp q).postcomp w) :=
    hl.trans ((heq_of_eq hs).trans hr.symm)
  exact functorIso_postcomp_iso_reflects_heq
    (eqToIso (coherentDiagramTotalVertex_object Z)).symm _ _
    (strictPullbackImage_eq p q (coherentCospanNativeCommonComparison F X Y Z C)).symm
    (strictPullbackImage_eq p q (coherentCospanModelCommonComparison F X Y Z C)).symm hh

end SerrePositivity.InfinityCategories.F2
