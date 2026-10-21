module

public import SerrePositivity.InfinityCategories.F2.CospanRectificationImages
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerHEq

/-!
概要：元の cospan 左厳密化の逆の底の像を、元の path の逆と元の値比較へ表示する。
方針：同じ厳密化の指定像を戻し、明示した端点の下で逆同型と合成を取る。
規約：元の path と値比較を保持。使われ方：共通の左脚の底の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Z X' Z' : SSet.{u}}
  [KanComplex X] [KanComplex Z] [KanComplex X'] [KanComplex Z']
  (f : X ⟶ Z) (f' : X' ⟶ Z') (s : X ⟶ X') (v : Z ⟶ Z')
  (e : FunctorIso (f ≫ v) (s ≫ f'))
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Z) f

/-- 左厳密化の逆の底の像は、同じ元の path の逆と元の指定比較の合成である。 -/
lemma cospanRectificationLeftIso_inverse_image :
    HEq (FunctorIso.postcomp (cospanRectificationLeftIso f f' s v e).symm
      (intervalReplacementEndpoint f'))
      ((functorIsoOfEq ((intervalReplacementPathIso f).postcomp v)
        (Category.assoc pr f v) rfl).symm ≪≫ e.precomp pr) := by
  let L := cospanRectificationLeftIso f f' s v e
  let d := functorIsoOfEq ((intervalReplacementPathIso f).postcomp v)
    (Category.assoc pr f v) rfl
  let core := FunctorIso.precomp e.symm pr ≪≫ d
  have h₀ := (functorIsoOfEq_heq (L.postcomp (intervalReplacementEndpoint f')) rfl
    (cospanRectificationLeftMap_over f f' s v e)).symm
  have h₁ := cospanRectificationLeftIso_image f f' s v e
  have h₂ : HEq (cospanRectificationLeftBaseIso f f' s v e) core := by
    dsimp only [cospanRectificationLeftBaseIso, core, d]
    exact functorIsoOfEq_heq _ _ _
  have hh := h₀.trans ((heq_of_eq h₁).trans h₂)
  have ht : (pr ≫ s ≫ intervalReplacementSection f') ≫ intervalReplacementEndpoint f' =
      pr ≫ (s ≫ f') := by simp only [Category.assoc, intervalReplacementSection_endpoint]
  have hs := cospanRectificationLeftMap_over f f' s v e
  have hi := functorIso_symm_heq_of_heq core (L.postcomp (intervalReplacementEndpoint f'))
    ht.symm hs.symm hh
  have hc : core.symm = d.symm ≪≫ e.precomp pr := by
    dsimp only [core]
    rw [Iso.trans_symm, ← functorIso_precomp_symm, Iso.symm_symm_eq]
  rw [functorIso_postcomp_symm]
  exact hi.trans (heq_of_eq hc)

end SerrePositivity.InfinityCategories.F2
