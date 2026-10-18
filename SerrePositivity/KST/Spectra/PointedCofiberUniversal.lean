module

public import SerrePositivity.KST.Spectra.PointedCofiber

/-!
概要：点つき cofiber の零合成による降下と一意性。
方針：cofiber の pushout の普遍性を零対象を経由する条件に直す。
規約：通常の点つき単体集合の cofiber。
使われ方：Goerss–Jardine I §7、VIII §1。cofiber とセルの余積の交換の構成。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)

@[reassoc (attr := simp)]
lemma pointedCofiberProjection_zero : i ≫ pointedCofiberProjection i = 0 := by
  rw [pointedCofiber_condition, PointedObject.toPoint_comp_fromPoint]

/-- 概要：i と合成して零となる点つき射を cofiber へ降ろす。
方針：零対象からの基点射と組にして pushout の降下を使う。
規約：条件は点つき圏の零射による等式。
使われ方：Goerss–Jardine I §7、VIII §1。セルごとの降下射の構成。 -/
def pointedCofiberDescOfZero (f : B ⟶ Z) (hf : i ≫ f = 0) : pointedCofiber i ⟶ Z :=
  (pointedCofiber_isPushout i).desc f (PointedObject.fromPoint Z) (by
    rw [PointedObject.toPoint_comp_fromPoint]
    exact hf)

@[reassoc (attr := simp)]
lemma pointedCofiberProjection_descOfZero (f : B ⟶ Z) (hf : i ≫ f = 0) :
    pointedCofiberProjection i ≫ pointedCofiberDescOfZero i f hf = f :=
  (pointedCofiber_isPushout i).inl_desc _ _ _

/-- 概要：cofiber からの点つき射は商写像への前合成で決まる。
方針：pushout の一意性を使い、零対象からの成分は一意とする。
規約：基礎の cofiber の具体的な商の定義に依存しない。
使われ方：Goerss–Jardine I §7、VIII §1。cofiber の比較の往復則。 -/
theorem pointedCofiber_hom_ext {f g : pointedCofiber i ⟶ Z}
    (h : pointedCofiberProjection i ≫ f = pointedCofiberProjection i ≫ g) : f = g :=
  (pointedCofiber_isPushout i).hom_ext h (PointedObject.point_isZero.eq_of_src _ _)

end

end SerrePositivity.KST.Spectra
