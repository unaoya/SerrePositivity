module
public import SerrePositivity.KST.SConstruction.CofiberTensorDesc

/-! # 元の cofiber の通常の cylinder からの降下
概要：潰す部分の cylinder を基点へ送る通常の写像を、元の cofiber と区間の積へ降ろす。
方針：通常の SSet の pushout を右テンソルで保存し、その二脚の普遍性を用いる。
規約：smash でなく通常の積。使われ方：点つき経路商の基点を固定する収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet

/-- 通常の cofiber の pushout は通常の右テンソルで保存される。 -/
lemma rawCofiberCylinderSquare {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    IsPushout (f ▷ K) (toUnit A ▷ K) (PointedObject.cofiberQuotient f ▷ K)
      ((PointedObject.cofiber f).hom ▷ K) :=
  (IsPushout.of_hasPushout f (toUnit A)).map (tensorRight K)

/-- 潰す部分の全 cylinder が基点へ写る射を、元の cofiber の通常の積から降ろす。 -/
def rawCofiberCylinderDesc {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u})
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ K ⟶ Z.right)
    (hf : (f ▷ K) ≫ h = toUnit (A ⊗ K) ≫ Z.hom) :
    (PointedObject.cofiber f).right ⊗ K ⟶ Z.right :=
  (rawCofiberCylinderSquare f K).desc h (toUnit ((𝟙_ SSet.{u}) ⊗ K) ≫ Z.hom)
    (by simpa only [comp_toUnit_assoc] using hf)

/-- 降ろした cylinder を元の商射へ引き戻すと元の射になる。 -/
lemma rawCofiberCylinderDesc_quotient {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u})
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ K ⟶ Z.right) (hf) :
    (PointedObject.cofiberQuotient f ▷ K) ≫ rawCofiberCylinderDesc f K Z h hf = h :=
  (rawCofiberCylinderSquare f K).inl_desc _ _ _

/-- 降ろした cylinder は区間全体で元の商の基点を標的の基点へ送る。 -/
lemma rawCofiberCylinderDesc_point {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u})
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ K ⟶ Z.right) (hf) :
    ((PointedObject.cofiber f).hom ▷ K) ≫ rawCofiberCylinderDesc f K Z h hf =
      toUnit ((𝟙_ SSet.{u}) ⊗ K) ≫ Z.hom :=
  (rawCofiberCylinderSquare f K).inr_desc _ _ _

/-- 元の商と基点の二つの cylinder 上の等号で、cofiber の cylinder からの射を検出する。 -/
lemma rawCofiberCylinder_hom_ext {A B Z : SSet.{u}} (f : A ⟶ B) (K : SSet.{u})
    (g h : (PointedObject.cofiber f).right ⊗ K ⟶ Z)
    (hq : (PointedObject.cofiberQuotient f ▷ K) ≫ g =
      (PointedObject.cofiberQuotient f ▷ K) ≫ h)
    (hp : ((PointedObject.cofiber f).hom ▷ K) ≫ g =
      ((PointedObject.cofiber f).hom ▷ K) ≫ h) : g = h :=
  (rawCofiberCylinderSquare f K).hom_ext hq hp

end SerrePositivity.KST.SConstruction
