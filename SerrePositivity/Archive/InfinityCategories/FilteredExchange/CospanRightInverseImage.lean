module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanRectificationImages
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq

/-!
概要：元の cospan 右厳密化の逆同型は、底で元の指定比較そのものに写る。
方針：同じ厳密化の指定像と端点補正を保持し、元の逆比較の逆を取る。
規約：端点の等式は元の脚の式から明示。使われ方：共通の右脚の底の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Z X' Z' : SSet.{u}}
  [KanComplex X] [KanComplex Z] [KanComplex X'] [KanComplex Z']
  (f : X ⟶ Z) (f' : X' ⟶ Z') (s : X ⟶ X') (v : Z ⟶ Z')
  (e : FunctorIso (f ≫ v) (s ≫ f'))

/-- 元の右厳密化の逆の底の像は、元の指定比較に型付きで一致する。 -/
lemma cospanRectificationRightIso_inverse_image :
    HEq (FunctorIso.postcomp (cospanRectificationRightIso f f' s v e).symm
      (intervalReplacementEndpoint f')) e := by
  let R := cospanRectificationRightIso f f' s v e
  have h₀ := (functorIsoOfEq_heq (R.postcomp (intervalReplacementEndpoint f')) rfl
    (cospanRectificationRightMap_over f f' s v e)).symm
  have h₁ := cospanRectificationRightIso_image f f' s v e
  have h₂ : HEq (cospanRectificationRightBaseIso f f' s v e) e.symm :=
    functorIsoOfEq_heq _ _ _
  have hh := h₀.trans ((heq_of_eq h₁).trans h₂)
  have ht : (s ≫ intervalReplacementSection f') ≫ intervalReplacementEndpoint f' =
      s ≫ f' := by rw [Category.assoc, intervalReplacementSection_endpoint]
  have hs := cospanRectificationRightMap_over f f' s v e
  have hi := functorIso_symm_heq_of_heq e.symm
    (R.postcomp (intervalReplacementEndpoint f')) ht.symm hs.symm hh
  rw [functorIso_postcomp_symm]
  exact hi

end SerrePositivity.InfinityCategories.F2
