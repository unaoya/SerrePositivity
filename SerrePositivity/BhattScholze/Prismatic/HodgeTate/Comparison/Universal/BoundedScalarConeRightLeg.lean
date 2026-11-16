module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.DerivedScalarConeRightLeg
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange

/-!
# 元の導来底変換の錐比較と右脚

## 概要
上に有界な導来底変換の元の錐比較は、同じ元の右脚を保つ。

## 方針
元の射影模型の錐の右脚の計算を、元の局所化比較で移す。

## 規約
元の比較同型と元の導来底変換を変更しない。

## 使われ方
元の二座標完備底変換の商射との整合性に使う。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B]

/-- 元の右脚を上に有界な対象の圏で見たもの。 -/
def boundedScalarConeRightLeg (a : R) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    X ⟶ (boundedAboveDerivedScalarCone R a).obj X :=
  ObjectProperty.homMk ((derivedScalarConeRightLeg R a).app X.obj)

/-- 元の射影模型上の錐への比較は元の右脚を保つ。 -/
theorem scalarConeRightLeg_model (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (P : BoundedAboveDerivedModel X.obj) :
    (derivedScalarConeRightLeg R a).app X.obj ≫
        ((derivedScalarConeFunctor R a).mapIso P.iso.symm ≪≫
          (derivedScalarConeComparison R a).app P.complex).hom =
      (boundedAboveDerivedConeInr P P (smulId a P.complex)).hom := by
  have hn := (derivedScalarConeRightLeg R a).naturality P.iso.inv
  simp only [Functor.id_map] at hn
  change _ = P.iso.inv ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr _) 
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom]
  rw [← Category.assoc, ← hn, Category.assoc, derivedScalarConeRightLeg_comparison]

/-- 同じ元の射の等式による錐の移送は右脚を保つ。 -/
theorem coneRightLeg_eqToHom {K : CochainComplex (ModuleCat.{u} B) ℤ}
    {f g : K ⟶ K} (h : f = g) :
    DerivedCategory.Q.map (CochainComplex.mappingCone.inr f) ≫
      eqToHom (congrArg (fun k => DerivedCategory.Q.obj (CochainComplex.mappingCone k)) h) =
    DerivedCategory.Q.map (CochainComplex.mappingCone.inr g) := by
  subst g
  simp

/-- スカラー底変換による元の錐比較は、同じ右脚を保つ。 -/
theorem boundedAboveDerivedBaseChangeScalarConeIso_rightLeg
    (φ : R →+* B) (a : R) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedBaseChange φ).map (boundedScalarConeRightLeg a X)).hom ≫
        (boundedAboveDerivedBaseChangeScalarConeIso φ a X).hom =
      (derivedScalarConeRightLeg B (φ a)).app
        ((boundedAboveDerivedBaseChange φ).obj X).obj := by
  let P := boundedAboveDerivedChosenModel X
  let e : (boundedAboveDerivedScalarCone R a).obj X ≅
      boundedAboveDerivedConeObject P P (smulId a P.complex) :=
    ObjectProperty.isoMk _
      ((derivedScalarConeFunctor R a).mapIso P.iso.symm ≪≫
        (derivedScalarConeComparison R a).app P.complex)
  have he : boundedScalarConeRightLeg a X ≫ e.hom =
      boundedAboveDerivedConeInr P P (smulId a P.complex) := by
    apply ObjectProperty.hom_ext
    exact scalarConeRightLeg_model a X P
  have hi := boundedAboveLeftDerivedConeIso_inr (ModuleCat.extendScalars φ)
    P P (smulId a P.complex)
  have hc := coneRightLeg_eqToHom (baseChange_smulId φ P.complex a)
  have hδ := (derivedScalarConeRightLeg B (φ a)).naturality
    (boundedAboveDerivedBaseChangeModelIso φ X P).inv
  simp only [Functor.id_map] at hδ
  simp only [boundedAboveDerivedBaseChangeScalarConeIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom]
  change ((boundedAboveDerivedBaseChange φ).map (boundedScalarConeRightLeg a X)).hom ≫
    ((boundedAboveDerivedBaseChange φ).map e.hom).hom ≫ _ = _
  have hm := congrArg (fun q => q.hom)
    ((boundedAboveDerivedBaseChange φ).map_comp (boundedScalarConeRightLeg a X) e.hom)
  change ((boundedAboveDerivedBaseChange φ).map
      (boundedScalarConeRightLeg a X ≫ e.hom)).hom =
    ((boundedAboveDerivedBaseChange φ).map (boundedScalarConeRightLeg a X)).hom ≫
      ((boundedAboveDerivedBaseChange φ).map e.hom).hom at hm
  rw [← Category.assoc, ← hm, he]
  erw [← Category.assoc, hi]
  erw [Category.assoc, reassoc_of% hc]
  have hl := derivedScalarConeRightLeg_comparison B (φ a) (baseChange φ P.complex)
  have hl' : DerivedCategory.Q.map (CochainComplex.mappingCone.inr
      (smulId (φ a) (baseChange φ P.complex))) ≫
      (derivedScalarConeComparison B (φ a)).inv.app (baseChange φ P.complex) =
      (derivedScalarConeRightLeg B (φ a)).app (DerivedCategory.Q.obj (baseChange φ P.complex)) := by
    simp only [← hl, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  erw [reassoc_of% hl', ← hδ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
