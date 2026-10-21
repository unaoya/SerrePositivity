module

public import SerrePositivity.InfinityCategories.F1.IntervalDiagramPushoutLift

/-!
概要：同じ二図式の両端固定区間 Hom は、底の pushout を厳密な pullback に写す。
方針：全パラメーターの貼り合わせと、その二つの制限と一意性を束ねる。
規約：分類先の元の Hom と元の制限そのものを使う。
使われ方：共有頂点を持つ区間と高次セルの Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {B X T : SSet.{u}} (F G : B ⟶ X) {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left)
  (s : T ⟶ intervalMappingSpace (functorVertex (c.hom ≫ F)) (functorVertex (c.hom ≫ G)))
  (t : T ⟶ intervalMappingSpace (functorVertex (b.hom ≫ F)) (functorVertex (b.hom ≫ G)))
  (hst : s ≫ intervalDiagramOverPre F G g = t ≫ intervalDiagramOverPre F G f)

/-- 同じ二図式の間の区間 Hom の族を、底の pushout 上へ貼る。 -/
def intervalDiagramPushoutLift :
    T ⟶ intervalMappingSpace (functorVertex (d.hom ≫ F)) (functorVertex (d.hom ≫ G)) :=
  intervalMappingCurryOfEndpoints (intervalDiagramPushoutUncurry F G f g i j hp s t hst)
    (intervalDiagramPushoutUncurry_zero F G f g i j hp s t hst)
    (intervalDiagramPushoutUncurry_one F G f g i j hp s t hst)

/-- 貼り合わせの最初の制限は元の区間 Hom の族。 -/
lemma intervalDiagramPushoutLift_fst :
    intervalDiagramPushoutLift F G f g i j hp s t hst ≫ intervalDiagramOverPre F G j = s := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry, intervalDiagramPushoutLift,
    intervalMappingUncurry_curryOfEndpoints, intervalDiagramPushoutUncurry_fst]

/-- 貼り合わせの二番目の制限も元の区間 Hom の族。 -/
lemma intervalDiagramPushoutLift_snd :
    intervalDiagramPushoutLift F G f g i j hp s t hst ≫ intervalDiagramOverPre F G i = t := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramOverPre_uncurry, intervalDiagramPushoutLift,
    intervalMappingUncurry_curryOfEndpoints, intervalDiagramPushoutUncurry_snd]

include hp in
/-- 元の二つの制限が等しければ、元の区間 Hom の族も等しい。 -/
lemma intervalDiagramPushout_hom_ext
    (x y : T ⟶ intervalMappingSpace (functorVertex (d.hom ≫ F)) (functorVertex (d.hom ≫ G)))
    (hc : x ≫ intervalDiagramOverPre F G j = y ≫ intervalDiagramOverPre F G j)
    (hb : x ≫ intervalDiagramOverPre F G i = y ≫ intervalDiagramOverPre F G i) : x = y := by
  apply intervalMappingUncurry_injective
  apply (isPullback_pre_of_isPushout hp X).hom_ext
  · simpa only [intervalDiagramOverPre_uncurry] using congrArg intervalMappingUncurry hc
  · simpa only [intervalDiagramOverPre_uncurry] using congrArg intervalMappingUncurry hb

include hp in
/-- 同じ両端固定区間 Hom は、底の pushout を厳密な pullback に写す。 -/
lemma intervalDiagramOverPre_isPullback_of_isPushout :
    IsPullback (intervalDiagramOverPre F G j) (intervalDiagramOverPre F G i)
      (intervalDiagramOverPre F G g) (intervalDiagramOverPre F G f) := by
  have hfg : f ≫ i = g ≫ j := Over.OverMorphism.ext hp.w
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [intervalDiagramOverPre_comp, intervalDiagramOverPre_comp, hfg]
  · intro T x y hc hb
    exact intervalDiagramPushout_hom_ext F G f g i j hp x y hc hb
  · intro T s t hst
    exact ⟨intervalDiagramPushoutLift F G f g i j hp s t hst,
      intervalDiagramPushoutLift_fst F G f g i j hp s t hst,
      intervalDiagramPushoutLift_snd F G f g i j hp s t hst⟩

end SerrePositivity.InfinityCategories
