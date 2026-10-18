module

public import SerrePositivity.KST.Spectra.PointedCofiber

/-!
概要：点つき pushout の対向する二つの cofiber の標準同型。
方針：元の pushout と cofiber の pushout を貼り合わせて余極限の一意性を使う。
規約：通常の cofiber の同型であり導来構造は使わない。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の相対商をセルの商へ移す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B C D : PointedSimplicialSet.{u}}
  {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}

/-- 概要：pushout の上側を潰すと左側を潰した cofiber の pushout になる。
方針：反転した元の正方形へ cofiber の正方形を縦に貼る。
規約：上側への複合から零対象への射は零対象の終対象性で同定する。
使われ方：Goerss–Jardine I §7、VIII §1。相対 cofiber の excision の厳密な形。 -/
theorem pointedCofiberPushout_isPushout (h : IsPushout t l r b) :
    IsPushout l (PointedObject.toPoint A) (b ≫ pointedCofiberProjection r)
      (PointedObject.fromPoint (pointedCofiber r)) := by
  have hp := h.flip.paste_vert (pointedCofiber_isPushout r)
  have ht : t ≫ PointedObject.toPoint B = PointedObject.toPoint A :=
    PointedObject.point_isZero.isTerminal.hom_ext _ _
  simpa only [ht] using hp

/-- 概要：点つき pushout の右辺の cofiber は左辺の cofiber と同型。
方針：貼り合わせた pushout と cofiber の標準 pushout の一意性を使う。
規約：同型の順射は下辺からの商写像と可換。
使われ方：Goerss–Jardine I §7、VIII §1。セルごとの商への比較。 -/
def pointedCofiberPushoutIso (h : IsPushout t l r b) :
    pointedCofiber r ≅ pointedCofiber l :=
  (pointedCofiberPushout_isPushout h).isoIsPushout _ _ (pointedCofiber_isPushout l)

@[reassoc]
lemma pointedCofiberPushoutIso_projection (h : IsPushout t l r b) :
    (b ≫ pointedCofiberProjection r) ≫ (pointedCofiberPushoutIso h).hom =
      pointedCofiberProjection l :=
  (pointedCofiberPushout_isPushout h).inl_isoIsPushout_hom _ _ (pointedCofiber_isPushout l)

end

end SerrePositivity.KST.Spectra
