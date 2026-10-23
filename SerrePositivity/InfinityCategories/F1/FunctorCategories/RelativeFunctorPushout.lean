module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPushoutLift

/-!
概要：始域の pushout を、元の相対関手空間の厳密な pullback へ写す。
方針：全パラメーターで貼った同じ族の二つの制限と一意性を確認する。
規約：充填性やモデル構造の仮定は不要。
使われ方：共有頂点を持つ区間の元の Hom の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {E B T : SSet.{u}} (q : E ⟶ B) {a b c d : Over B}
variable (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
variable (hp : IsPushout f.left g.left i.left j.left)
variable (s : T ⟶ relativeFunctorSpace q c.hom) (t : T ⟶ relativeFunctorSpace q b.hom)
variable (hst : s ≫ relativeFunctorOverPre q g = t ≫ relativeFunctorOverPre q f)

/-- 貼った相対族の最初の制限は、指定した元の族。 -/
lemma relativeFunctorPushoutLift_fst :
    relativeFunctorPushoutLift q f g i j hp s t hst ≫ relativeFunctorOverPre q j = s := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, relativeFunctorOverPre_ι, ← Category.assoc,
    relativeFunctorPushoutLift_ι, relativeFunctorPushoutUnrestrictedLift_fst]

/-- 貼った相対族の二番目の制限も、指定した元の族。 -/
lemma relativeFunctorPushoutLift_snd :
    relativeFunctorPushoutLift q f g i j hp s t hst ≫ relativeFunctorOverPre q i = t := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, relativeFunctorOverPre_ι, ← Category.assoc,
    relativeFunctorPushoutLift_ι, relativeFunctorPushoutUnrestrictedLift_snd]

include hp in
/-- 二つの制限が同じなら、元の相対族も厳密に同じ。 -/
lemma relativeFunctorPushout_hom_ext (x y : T ⟶ relativeFunctorSpace q d.hom)
    (hc : x ≫ relativeFunctorOverPre q j = y ≫ relativeFunctorOverPre q j)
    (hb : x ≫ relativeFunctorOverPre q i = y ≫ relativeFunctorOverPre q i) : x = y := by
  apply vertexFiber_hom_ext
  apply (isPullback_pre_of_isPushout hp E).hom_ext
  · simpa only [Category.assoc, relativeFunctorOverPre_ι] using
      congrArg (fun z ↦ z ≫ vertexFiberι _ _) hc
  · simpa only [Category.assoc, relativeFunctorOverPre_ι] using
      congrArg (fun z ↦ z ≫ vertexFiberι _ _) hb

include hp in
/-- 始域の pushout は、固定した射影への元の相対 Hom の実際の pullback を与える。 -/
lemma relativeFunctorOverPre_isPullback_of_isPushout :
    IsPullback (relativeFunctorOverPre q j) (relativeFunctorOverPre q i)
      (relativeFunctorOverPre q g) (relativeFunctorOverPre q f) := by
  have hfg : f ≫ i = g ≫ j := by
    apply Over.OverMorphism.ext
    exact hp.w
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← relativeFunctorOverPre_comp, ← relativeFunctorOverPre_comp, hfg]
  · intro T x y hc hb
    exact relativeFunctorPushout_hom_ext q f g i j hp x y hc hb
  · intro T s t hst
    exact ⟨relativeFunctorPushoutLift q f g i j hp s t hst,
      relativeFunctorPushoutLift_fst q f g i j hp s t hst,
      relativeFunctorPushoutLift_snd q f g i j hp s t hst⟩

end SerrePositivity.InfinityCategories
