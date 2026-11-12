module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.SSetPullbackColimit

/-!
概要：二つの余極限 cocone の各項で成り立つ底変換の pullback 性の全体への降下。
方針：比較の標準 pullback へ cocone を延長し、その余極限性と一意性から同型を得る。
規約：通常の単体集合の小さい余極限を扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱の pushout と底変換の交換。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：底上の二つの余極限の各項で比較が pullback なら全体の比較も pullback。
方針：全体の pullback への持ち上げで cocone を延長し、各脚の pullback 性で余極限にする。
規約：各項の底への射は cocone の脚と指定した係数射の合成。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底変換後の写像円柱を元の円柱の pullback と同定する。 -/
lemma sset_isPullback_of_colimits {J : Type v} [Category.{w} J] [Small.{u} J]
    {D E : J ⥤ SSet.{u}} (c : Cocone D) (hc : IsColimit c)
    (d : Cocone E) (hd : IsColimit d) (α : E ⟶ D) (a : d.pt ⟶ c.pt)
    {S T : SSet.{u}} (p : c.pt ⟶ S) (q : d.pt ⟶ T) (h : T ⟶ S)
    (hw : a ≫ p = q ≫ h) (ha : ∀ j, d.ι.app j ≫ a = α.app j ≫ c.ι.app j)
    (hp : ∀ j, IsPullback (α.app j) (d.ι.app j ≫ q) (c.ι.app j ≫ p) h) :
    IsPullback a q p h := by
  let l := pullback.lift a q hw
  let e := d.extend l
  have he : IsColimit e := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.sset_isColimit_of_pullback c hc e α (pullback.fst p h)
    intro j
    have ht : IsPullback (e.ι.app j ≫ pullback.snd p h) (α.app j)
        h (c.ι.app j ≫ p) := by
      change IsPullback ((d.ι.app j ≫ l) ≫ pullback.snd p h) (α.app j) h (c.ι.app j ≫ p)
      rw [Category.assoc, pullback.lift_snd]
      exact (hp j).flip
    apply ht.of_right _ (IsPullback.of_hasPullback p h).flip
    change (d.ι.app j ≫ l) ≫ pullback.fst p h = α.app j ≫ c.ι.app j
    rw [Category.assoc, pullback.lift_fst]
    exact ha j
  have hl : l = (hd.coconePointUniqueUpToIso he).hom := by
    apply hd.hom_ext
    intro j
    exact (hd.comp_coconePointUniqueUpToIso_hom he j).symm
  have : IsIso l := by
    rw [hl]
    infer_instance
  apply IsPullback.of_iso_pullback ⟨hw⟩ (asIso l)
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
