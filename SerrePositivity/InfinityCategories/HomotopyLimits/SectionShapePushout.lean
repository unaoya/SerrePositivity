module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PullbackSections
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：図式の形状の押し出しに沿って、底を保つ切断の族を厳密に貼り合わせる。
方針：パラメータとの直積が押し出しを保つことを使い、相対 curry で切断空間へ戻す。
規約：底上の射の可換条件を保持し、充填性や quasicategory 性を要求しない。
使われ方：任意の coherent な図式の余極限を、境界を固定した骨格の貼り合わせへ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E S T : SSet.{u}} (q : E ⟶ S)
  {A B C D : Over S} (f : A ⟶ B) (g : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
  (hp : IsPushout f.left g.left i.left j.left)

include hp in
/-- 形状の押し出し上の相対関手の族は、共通部分で一致する二つの族の唯一の貼り合わせ。 -/
lemma relativeFunctorOverPre_pushout_lift
    (a : T ⟶ relativeFunctorSpace q B.hom) (b : T ⟶ relativeFunctorSpace q C.hom)
    (hab : a ≫ relativeFunctorOverPre q f = b ≫ relativeFunctorOverPre q g) :
    ∃! t : T ⟶ relativeFunctorSpace q D.hom,
      t ≫ relativeFunctorOverPre q i = a ∧ t ≫ relativeFunctorOverPre q j = b := by
  let hs := hp.map (tensorRight T)
  have hc : (f.left ▷ T) ≫ relativeFunctorUncurry a =
      (g.left ▷ T) ≫ relativeFunctorUncurry b := by
    rw [← relativeFunctorOverPre_uncurry, hab, relativeFunctorOverPre_uncurry]
  let H := hs.desc (relativeFunctorUncurry a) (relativeFunctorUncurry b) hc
  have hH : H ≫ q = fst D.left T ≫ D.hom := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, relativeFunctorUncurry_projection]
      change fst B.left T ≫ B.hom = (i.left ▷ T) ≫ fst D.left T ≫ D.hom
      rw [whiskerRight_fst_assoc, i.w]
    · rw [← Category.assoc, hs.inr_desc, relativeFunctorUncurry_projection]
      change fst C.left T ≫ C.hom = (j.left ▷ T) ≫ fst D.left T ≫ D.hom
      rw [whiskerRight_fst_assoc, j.w]
  let t := relativeFunctorCurry H hH
  have ht : relativeFunctorUncurry t = H := relativeFunctorUncurry_curry _ _
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · apply relativeFunctorUncurry_injective q B.hom
    rw [relativeFunctorOverPre_uncurry, ht]
    exact hs.inl_desc _ _ _
  · apply relativeFunctorUncurry_injective q C.hom
    rw [relativeFunctorOverPre_uncurry, ht]
    exact hs.inr_desc _ _ _
  · intro m hm
    apply relativeFunctorUncurry_injective q D.hom
    rw [ht]
    apply hs.hom_ext
    · change (i.left ▷ T) ≫ relativeFunctorUncurry m = (i.left ▷ T) ≫ H
      rw [← relativeFunctorOverPre_uncurry, hm.1]
      exact (hs.inl_desc _ _ _).symm
    · change (j.left ▷ T) ≫ relativeFunctorUncurry m = (j.left ▷ T) ≫ H
      rw [← relativeFunctorOverPre_uncurry, hm.2]
      exact (hs.inr_desc _ _ _).symm

include hp in
/-- 図式の形状の押し出しは、相対関手空間の厳密な引き戻しを与える。 -/
lemma relativeFunctorOverPre_isPullback_of_pushout :
    IsPullback (relativeFunctorOverPre q i) (relativeFunctorOverPre q j)
      (relativeFunctorOverPre q f) (relativeFunctorOverPre q g) := by
  have hw : relativeFunctorOverPre q i ≫ relativeFunctorOverPre q f =
      relativeFunctorOverPre q j ≫ relativeFunctorOverPre q g := by
    rw [← relativeFunctorOverPre_comp, ← relativeFunctorOverPre_comp]
    congr 1
    apply (Over.forget S).map_injective
    exact hp.w
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  apply PullbackCone.isLimitAux'
  intro s
  have h := relativeFunctorOverPre_pushout_lift q f g i j hp s.fst s.snd s.condition
  exact ⟨h.choose, h.choose_spec.1.1, h.choose_spec.1.2,
    fun {_} h₁ h₂ ↦ h.choose_spec.2 _ ⟨h₁, h₂⟩⟩

include hp in
/-- 切断の族の貼り合わせを、二つの切断空間の引き戻しとの実際の同型に束ねる。 -/
def relativeFunctorOverPre_pushoutIso :
    relativeFunctorSpace q D.hom ≅
      pullback (relativeFunctorOverPre q f) (relativeFunctorOverPre q g) :=
  (relativeFunctorOverPre_isPullback_of_pushout q f g i j hp).isoPullback

end
end SerrePositivity.InfinityCategories.HomotopyLimits
