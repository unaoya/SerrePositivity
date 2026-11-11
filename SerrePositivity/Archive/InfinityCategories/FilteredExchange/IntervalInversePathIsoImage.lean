module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPathIso

/-!
概要：左厳密化で使う元の逆 path の指定像を、標的同型の往復の後で回収する。
方針：端点補正を保持して逆と前後合成を交換し、同じ標的同型の往復を消去する。
規約：元の path の指定類を保持。使われ方：左脚の補正像における native path の逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A X Z Z' : SSet.{u}} [KanComplex Z]
  (f : X ⟶ Z) (a : A ⟶ intervalReplacement f) (i : Z ≅ Z')
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Z) f

/-- 同じ端点補正付き逆 path の像は、元の path の同じ制限の逆に型付きで戻る。 -/
lemma intervalReplacementInversePathIso_image :
    HEq ((FunctorIso.precomp
      (functorIsoOfEq ((intervalReplacementPathIso f).postcomp i.hom)
        (Category.assoc pr f i.hom) rfl).symm a).postcomp i.inv)
      ((intervalReplacementPathIso f).precomp a).symm := by
  let P := intervalReplacementPathIso f
  have hc := functorIsoOfEq_symm_precomp_postcomp_heq (P.postcomp i.hom)
    (Category.assoc pr f i.hom) rfl a i.inv
  have he : (FunctorIso.precomp (P.postcomp i.hom).symm a).postcomp i.inv =
      (FunctorIso.postcomp (P.precomp a).symm i.hom).postcomp i.inv := by
    rw [functorIso_precomp_symm, ← functorIso_precomp_postcomp P a i.hom,
      ← functorIso_postcomp_symm]
  exact hc.trans ((heq_of_eq he).trans (functorIso_postcomp_iso_cancel (P.precomp a).symm i))

end SerrePositivity.InfinityCategories.F2
