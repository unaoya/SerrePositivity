module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullCalculation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionResolution

/-! # 外側右制限と全導来中間比較を組み合わせた任意モデル計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "LP" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A C D E F) Q.obj
local notation "GP" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B K D G) LP
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))

/-- 指定モデルから、入力の右制限表示と全導来外側右比較を続けた射。 -/
def restrictedMiddleModelPrefix :=
    (derivedBimoduleComposeResolutionComputation A K D E hE RQ R q hq).inv.app
        ((bimoduleToDerived A K D).obj GP) ≫
      ((derivedBimoduleComposeFunctor A K D E hE).obj ((bimoduleToDerived A D E).obj RQ)).map
        ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app
        ((bimoduleToDerived A D E).obj RQ)).app ((bimoduleToDerived A B D).obj LP)

private lemma paste_model_square
    {X Y : Type*} [Category* X] [Category* Y] (V : X ⥤ Y)
    {a b : Y} {x y z : X} (s : x ≅ y) (f : x ⟶ z)
    (h : a ⟶ V.obj x) (g : a ⟶ b) (e : b ⟶ V.obj y) (t : b ⟶ V.obj z)
    (h₁ : h ≫ V.map s.hom = g ≫ e) (h₂ : e ≫ V.map (s.inv ≫ f) = t) :
    h ≫ V.map f = g ≫ t := by
  have hs : h = g ≫ e ≫ V.map s.inv := by
    have hh := congrArg (fun k => k ≫ V.map s.inv) h₁
    simpa only [Category.assoc, ← V.map_comp, s.hom_inv_id, V.map_id,
      Category.comp_id] using hh
  rw [hs]
  simp only [Category.assoc]
  rw [← V.map_comp, h₂]

/-- 外側・中間の実際の全導来比較を、同じ指定解像度で通常の比較射へ計算する。 -/
lemma derivedBimoduleRestriction_model_calculation :
    restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq ≫
      (RG).map
        ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
          ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
            ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map (composeRightRestrictionIso A B K D E G LP R.obj).hom ≫
      (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  let s := middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq
  let b := (bimoduleToDerived A K E).map
    (composeRightRestrictionIso A B K D E G LP R.obj).hom
  let e := (middleRightRestrictionDerivedIso A B K G E).hom.app
    ((composeWith A B D E R.obj).obj LP)
  have hc := derivedBimoduleComposeRightRestrictionIso_resolution_app_calc
    A B K D E G hE RQ R q hq LP
  have hs : s.hom =
      (derivedBimoduleComposeResolutionComputation A B D E hE RQ R q hq).hom.app
        ((bimoduleToDerived A B D).obj LP) := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  apply paste_model_square (RG) s
    ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
      ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom)
    (restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq) b e
  · simpa only [hs, restrictedMiddleModelPrefix, Category.assoc] using hc
  · exact derivedMiddleRestrictionNatTrans_resolution_output_restriction
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (hE := hE)
      (P := P) (Q := Q) (R := R) (q := q) (hq := hq) (K := K) (G := G)

end SerrePositivity.DifferentialGraded.BimoduleTensor
