module

public import SerrePositivity.KST.Spectra.PathContractibility
public import SerrePositivity.Spectra.Pointed.Cofiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：商からの基点付き写像空間への、任意のパラメーターを持つ写像族の降下。
方針：商の pushout をパラメーターと tensor し、基点の等化子へ持ち上げる。
規約：Kan 性を使わない厳密な普遍性。使われ方：区間 end と円の写像空間の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra

/-- 商の pushout に tensor した、パラメーター付き写像族の降下。 -/
def cofiberFamilyDescRaw {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u}) (a : L ⊗ P ⟶ Z.right)
    (ha : (f ▷ P) ≫ a = toUnit (K ⊗ P) ≫ Z.hom) :
    (PointedObject.cofiber f).right ⊗ P ⟶ Z.right :=
  ((IsPushout.of_hasPushout f (toUnit K)).map ((tensoringRight SSet).obj P)).desc
    a (toUnit (𝟙_ SSet ⊗ P) ≫ Z.hom) (by simpa using ha)

/-- 降下した族は、商写像に沿って元の族へ厳密に戻る。 -/
@[reassoc (attr := simp)]
lemma cofiberFamilyDescRaw_quotient {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u}) (a : L ⊗ P ⟶ Z.right) (ha) :
    (PointedObject.cofiberQuotient f ▷ P) ≫ cofiberFamilyDescRaw f Z a ha = a :=
  ((IsPushout.of_hasPushout f (toUnit K)).map ((tensoringRight SSet).obj P)).inl_desc _ _ _

/-- 降下した族は、商の基点上で常に標的の基点を取る。 -/
@[reassoc (attr := simp)]
lemma cofiberFamilyDescRaw_basepoint {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u}) (a : L ⊗ P ⟶ Z.right) (ha) :
    ((PointedObject.cofiber f).hom ▷ P) ≫ cofiberFamilyDescRaw f Z a ha =
      toUnit (𝟙_ SSet ⊗ P) ≫ Z.hom :=
  ((IsPushout.of_hasPushout f (toUnit K)).map ((tensoringRight SSet).obj P)).inr_desc _ _ _

/-- 境界の像を基点へ送る族は、商からの基点付き写像空間へ降下する。 -/
def cofiberFamilyDesc {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u}) (a : L ⊗ P ⟶ Z.right)
    (ha : (f ▷ P) ≫ a = toUnit (K ⊗ P) ≫ Z.hom) :
    P ⟶ (PointedObject.basedHom (PointedObject.cofiber f) Z).right :=
  equalizer.lift (curry (cofiberFamilyDescRaw f Z a ha)) (by
    change curry _ ≫ (pre (PointedObject.cofiber f).hom).app Z.right =
      curry _ ≫ (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Z)
    rw [curry_pre_app, cofiberFamilyDescRaw_basepoint,
      PointedObject.curry_constant, comp_toUnit_assoc]
    rfl)

/-- 写像空間への降下を元の対象へ制限すると、元の族の curry となる。 -/
@[reassoc]
lemma cofiberFamilyDesc_restriction {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u}) (a : L ⊗ P ⟶ Z.right) (ha) :
    cofiberFamilyDesc f Z a ha ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        (pre (PointedObject.cofiberQuotient f)).app Z.right = curry a := by
  rw [cofiberFamilyDesc, ← Category.assoc]
  dsimp only [PointedObject.basedHomι]
  rw [equalizer.lift_ι, curry_pre_app, cofiberFamilyDescRaw_quotient]

/-- 商からの基点付き写像の族は、元の対象への制限で一意に決まる。 -/
lemma cofiberFamily_hom_ext {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u})
    {a b : P ⟶ (PointedObject.basedHom (PointedObject.cofiber f) Z).right}
    (h : a ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        (pre (PointedObject.cofiberQuotient f)).app Z.right =
      b ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        (pre (PointedObject.cofiberQuotient f)).app Z.right) : a = b := by
  apply (cancel_mono (PointedObject.basedHomι (PointedObject.cofiber f) Z)).mp
  apply uncurry_injective
  apply ((IsPushout.of_hasPushout f (toUnit K)).map
    ((tensoringRight SSet).obj P)).hom_ext
  · change (PointedObject.cofiberQuotient f ▷ P) ≫ uncurry _ =
      (PointedObject.cofiberQuotient f ▷ P) ≫ uncurry _
    simpa only [← uncurry_pre_app, Category.assoc] using congrArg uncurry h
  · change ((PointedObject.cofiber f).hom ▷ P) ≫ uncurry _ =
      ((PointedObject.cofiber f).hom ▷ P) ≫ uncurry _
    rw [← uncurry_pre_app, ← uncurry_pre_app]
    apply congrArg uncurry
    change a ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        PointedObject.homRestriction (PointedObject.cofiber f) Z =
      b ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        PointedObject.homRestriction (PointedObject.cofiber f) Z
    rw [PointedObject.basedHomι_condition]
    simp only [PointedObject.homConstant, comp_toUnit_assoc]

/-- 基点付き写像空間の任意の族は、源の基点上で標的の基点を取る。 -/
lemma basedHomFamily_basepoint {P : SSet.{u}} (X Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Z).right) :
    (X.hom ▷ P) ≫ uncurry (a ≫ PointedObject.basedHomι X Z) =
      toUnit (𝟙_ SSet ⊗ P) ≫ Z.hom := by
  rw [← uncurry_pre_app]
  change uncurry (a ≫ PointedObject.basedHomι X Z ≫ PointedObject.homRestriction X Z) = _
  rw [PointedObject.basedHomι_condition]
  simp only [PointedObject.homConstant, comp_toUnit_assoc]
  change uncurry (toUnit P ≫ curry (toUnit (𝟙_ SSet.{u} ⊗ 𝟙_ SSet.{u}) ≫ Z.hom)) = _
  rw [← PointedObject.curry_constant, uncurry_curry]

/-- 商の写像空間の族を元の対象へ制限すると、境界上で基点を取る。 -/
lemma cofiberFamily_restriction_boundary {K L P : SSet.{u}} (f : K ⟶ L)
    (Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom (PointedObject.cofiber f) Z).right) :
    (f ▷ P) ≫ uncurry (a ≫ PointedObject.basedHomι (PointedObject.cofiber f) Z ≫
        (pre (PointedObject.cofiberQuotient f)).app Z.right) =
      toUnit (K ⊗ P) ≫ Z.hom := by
  rw [← Category.assoc, uncurry_pre_app, ← comp_whiskerRight_assoc,
    PointedObject.cofiberQuotient_condition, comp_whiskerRight_assoc,
    basedHomFamily_basepoint, comp_toUnit_assoc]

end SerrePositivity.KST.Spectra
