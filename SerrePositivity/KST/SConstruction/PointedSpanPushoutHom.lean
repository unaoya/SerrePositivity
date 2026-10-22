module
public import SerrePositivity.KST.SConstruction.PointedSpanPushout
public import SerrePositivity.KST.SConstruction.EnrichedCoconeFamily

/-! # 元の span の標準 end から実押し出しへの全 Hom 作用
概要：元の全自然変換族を、同じ実押し出しの basedHom へ降ろす。
方針：両端で余錐成分を後合成し、元の二脚の自然性を使って貼り合わせる。
規約：両包含で同じ全入力族を回収する。使われ方：関手的 homotopy pushout。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 全自然変換族の左成分を、元の左包含で後合成する。 -/
def pointedSpanPushoutLeftFamily (X Y : PointedSpanDiagram.{u}) :
    (X ⟶[SSet.{u}] Y) ⟶ (X.diagram.obj .left ⟶[SSet.{u}] pointedSpanPushout Y) :=
  pointedSpanProjection X Y .left ≫
    eHomWhiskerLeft SSet (X.diagram.obj .left) (pointedSpanPushoutInl Y)

/-- 全自然変換族の右成分を、元の右包含で後合成する。 -/
def pointedSpanPushoutRightFamily (X Y : PointedSpanDiagram.{u}) :
    (X ⟶[SSet.{u}] Y) ⟶ (X.diagram.obj .right ⟶[SSet.{u}] pointedSpanPushout Y) :=
  pointedSpanProjection X Y .right ≫
    eHomWhiskerLeft SSet (X.diagram.obj .right) (pointedSpanPushoutInr Y)

/-- 元の二脚の自然性は、同じ実押し出しへの全族の貼り合わせ条件を与える。 -/
lemma pointedSpanPushoutFamily_condition (X Y : PointedSpanDiagram.{u}) :
    pointedSpanPushoutLeftFamily X Y ≫
        eHomWhiskerRight SSet (X.diagram.map WalkingSpan.Hom.fst) (pointedSpanPushout Y) =
      pointedSpanPushoutRightFamily X Y ≫
        eHomWhiskerRight SSet (X.diagram.map WalkingSpan.Hom.snd) (pointedSpanPushout Y) := by
  change (pointedSpanProjection X Y .left ≫ _) ≫ _ =
    (pointedSpanProjection X Y .right ≫ _) ≫ _
  rw [enriched_cocone_family SSet _ _ _ _ _
    (pointedSpanProjection_naturality X Y WalkingSpan.Hom.fst)]
  rw [enriched_cocone_family SSet _ _ _ _ _
    (pointedSpanProjection_naturality X Y WalkingSpan.Hom.snd)]
  rw [pointedSpanPushout_condition Y]

/-- 元の全自然変換の、同じ実押し出しへの全 basedHom 作用。 -/
def pointedSpanPushoutHom (X Y : PointedSpanDiagram.{u}) :
    (X ⟶[SSet.{u}] Y) ⟶ (pointedSpanPushout X ⟶[SSet.{u}] pointedSpanPushout Y) :=
  pointedPushoutFamilyDesc (pointedSpanPushoutLeftMap X) (pointedSpanPushoutRightMap X)
    (pointedSpanPushoutLeftFamily X Y) (pointedSpanPushoutRightFamily X Y) (by
      have h := pointedSpanPushoutFamily_condition X Y
      rw [pointedSSetObject_whiskerRight, pointedSSetObject_whiskerRight] at h
      exact h)

/-- 全 Hom 作用は、元の左包含上で同じ全入力族を回収する。 -/
lemma pointedSpanPushoutHom_inl (X Y : PointedSpanDiagram.{u}) :
    pointedSpanPushoutHom X Y ≫
        eHomWhiskerRight SSet (pointedSpanPushoutInl X) (pointedSpanPushout Y) =
      pointedSpanPushoutLeftFamily X Y := by
  rw [pointedSSetObject_whiskerRight]
  exact pointedPushoutFamilyDesc_inl (pointedSpanPushoutLeftMap X)
    (pointedSpanPushoutRightMap X) (pointedSpanPushoutLeftFamily X Y)
    (pointedSpanPushoutRightFamily X Y) _

/-- 全 Hom 作用は、元の右包含上で同じ全入力族を回収する。 -/
lemma pointedSpanPushoutHom_inr (X Y : PointedSpanDiagram.{u}) :
    pointedSpanPushoutHom X Y ≫
        eHomWhiskerRight SSet (pointedSpanPushoutInr X) (pointedSpanPushout Y) =
      pointedSpanPushoutRightFamily X Y := by
  rw [pointedSSetObject_whiskerRight]
  exact pointedPushoutFamilyDesc_inr (pointedSpanPushoutLeftMap X)
    (pointedSpanPushoutRightMap X) (pointedSpanPushoutLeftFamily X Y)
    (pointedSpanPushoutRightFamily X Y) _

/-- 元の両包含は、全パラメータの押し出し Hom の等号を検出する。 -/
lemma pointedSpanPushoutHom_ext (X : PointedSpanDiagram.{u}) (Z : PointedSSetObject.{u})
    {P : SSet.{u}} {a b : P ⟶ (pointedSpanPushout X ⟶[SSet.{u}] Z)}
    (hl : a ≫ eHomWhiskerRight SSet (pointedSpanPushoutInl X) Z =
      b ≫ eHomWhiskerRight SSet (pointedSpanPushoutInl X) Z)
    (hr : a ≫ eHomWhiskerRight SSet (pointedSpanPushoutInr X) Z =
      b ≫ eHomWhiskerRight SSet (pointedSpanPushoutInr X) Z) : a = b :=
  pointedPushoutFamily_ext (pointedSpanPushoutLeftMap X) (pointedSpanPushoutRightMap X)
    (by
      rw [pointedSSetObject_whiskerRight] at hl
      exact hl)
    (by
      rw [pointedSSetObject_whiskerRight] at hr
      exact hr)

end SerrePositivity.KST.SConstruction
