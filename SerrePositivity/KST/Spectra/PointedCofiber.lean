module

public import SerrePositivity.KST.Spectra.PointedEnrichment
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：点つき射の基礎 cofiber の点つき pushout としての普遍性。
方針：基礎単体集合で像を基点へ潰す商を点つき圏へ戻す。
規約：導来 cofiber の主張ではなく通常の pushout。
使われ方：Goerss–Jardine I §7、HTT A.3.3。loop と path fiber の内部 Hom による比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)

/-- 概要：点つき射の像を基点へ潰した通常の cofiber。
方針：基礎単体集合の cofiber を用いる。
規約：像には元の基点も含まれる。
使われ方：Goerss–Jardine I §7。loop の源の商。 -/
abbrev pointedCofiber : PointedSimplicialSet.{u} := PointedObject.cofiber i.right

/-- 概要：標的から点つき cofiber への商写像。
方針：元の基点も像に含まれることを使う。
規約：基礎射は既存の cofiberQuotient。
使われ方：Goerss–Jardine I §7。点つき pushout の上辺。 -/
def pointedCofiberProjection : Y ⟶ pointedCofiber i :=
  Under.homMk (PointedObject.cofiberQuotient i.right) (by
    rw [← Under.w i, Category.assoc, PointedObject.cofiberQuotient_condition]
    simp only [comp_toUnit_assoc, toUnit_unit, Category.id_comp])

/-- 概要：商写像は i の像を基点へ送る。
方針：基礎 cofiber の関係式を使う。
規約：点つき圏の零対象を経由する射との等式。
使われ方：Goerss–Jardine I §7、HTT A.3.3。pushout の可換条件。 -/
theorem pointedCofiber_condition : i ≫ pointedCofiberProjection i =
    PointedObject.toPoint X ≫ PointedObject.fromPoint (pointedCofiber i) := by
  apply Under.UnderMorphism.ext
  exact PointedObject.cofiberQuotient_condition i.right

/-- 概要：i の像を基点へ送る点つき射は cofiber へ降りる。
方針：基礎 cofiber の普遍性を使う。
規約：零対象への射と同じ合成を持つことを明示する。
使われ方：Goerss–Jardine I §7。pushout の普遍性。 -/
def pointedCofiberDesc (s : PushoutCocone i (PointedObject.toPoint X)) :
    pointedCofiber i ⟶ s.pt :=
  PointedObject.cofiberDesc i.right s.pt s.inl.right (by
    have hs : s.inr.right = s.pt.hom := by simpa [PointedObject.point] using Under.w s.inr
    have hc := congrArg Under.Hom.right s.condition
    simpa only [Under.comp_right, PointedObject.toPoint, Under.homMk_right, hs] using hc)

/-- 概要：点つき cofiber の自然な pushout cocone。
方針：商写像と零対象からの基点射を組み合わせる。
規約：入力 span は i と X から零対象への射。
使われ方：HTT A.3.3、Goerss–Jardine I §7。内部 Hom で引き戻す正方形。 -/
def pointedCofiberCocone : PushoutCocone i (PointedObject.toPoint X) :=
  PushoutCocone.mk (pointedCofiberProjection i) (PointedObject.fromPoint (pointedCofiber i))
    (pointedCofiber_condition i)

/-- 概要：点つき cofiber cocone は余極限。
方針：商からの降下と cofiber の射の外延性を使う。
規約：通常の点つき単体集合の余極限。
使われ方：Goerss–Jardine I §7、HTT A.3.3。Hom の fiber の普遍性。 -/
def pointedCofiberIsColimit : IsColimit (pointedCofiberCocone i) := by
  refine PushoutCocone.IsColimit.mk (pointedCofiber_condition i)
    (pointedCofiberDesc i) ?_ ?_ ?_
  · intro s
    apply Under.UnderMorphism.ext
    exact PointedObject.cofiberQuotient_desc _ _ _ _
  · intro s
    exact PointedObject.point_isZero.eq_of_src _ _
  · intro s m hm _
    apply PointedObject.cofiber_hom_ext i.right
    rw [pointedCofiberDesc, PointedObject.cofiberQuotient_desc]
    exact congrArg Under.Hom.right hm

/-- 概要：点つき射の cofiber は零対象への射との pushout。
方針：構成済みの cocone と余極限性を束ねる。
規約：安定圏や導来 cofiber は仮定しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。loop と path fiber の比較。 -/
theorem pointedCofiber_isPushout : IsPushout i (PointedObject.toPoint X)
    (pointedCofiberProjection i) (PointedObject.fromPoint (pointedCofiber i)) where
  w := pointedCofiber_condition i
  isColimit' := ⟨pointedCofiberIsColimit i⟩

end

end SerrePositivity.KST.Spectra
