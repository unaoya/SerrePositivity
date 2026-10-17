module

public import SerrePositivity.HomologicalAlgebra.AlgebraBaseChangeTensorH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeH0Coefficient

/-! # 実完備底変換と元の導来 tensor の標準単位の一致 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (a : R)

/-- 元の実完備底変換を係数制限し、正規化した実完備 tensor へ比較する。 -/
def completedAlgebraBaseChangeTensorIso :
    (derivedRestrictScalars (algebraMap R B)).obj
      ((derivedComplexCompletionFunctor B (algebraMap R B a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) ≅
      (boundedAboveCompletedTensorAlgebra R a B S).X.obj :=
  ((derivedCompletionRestrictionIso (algebraMap R B) a).app _).symm ≪≫
    (derivedComplexCompletionFunctor R a).mapIso (algebraBaseChangeTensorIso R B S)

/-- 新しい対象を選ばず、既存の係数正規化を含む G2 の比較そのものに等しい。 -/
theorem completedAlgebraBaseChangeTensorIso_eq :
    completedAlgebraBaseChangeTensorIso R B S a =
      DerivedCategory.Minus.ι.mapIso
        (completedBaseChangeTensorRestrictionIso (algebraMap R B) a
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))) ≪≫
      DerivedCategory.Minus.ι.mapIso (completedScalarTensorNormalizationIso R B S a) := by
  apply Iso.ext
  simp only [completedAlgebraBaseChangeTensorIso, completedBaseChangeTensorRestrictionIso,
    completedScalarTensorNormalizationIso, algebraBaseChangeTensorIso,
    baseChangeScalarNormalizationIso, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- 完備底変換の元の単位は、比較を通して元の tensor 完備化単位になる。 -/
theorem completedAlgebraBaseChangeTensorIso_unit :
    (derivedRestrictScalars (algebraMap R B)).map
        ((derivedComplexCompletionUnit B (algebraMap R B a)).app
          ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) ≫
      (completedAlgebraBaseChangeTensorIso R B S a).hom =
    (algebraBaseChangeTensorIso R B S).hom ≫
      (derivedComplexCompletionUnit R a).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj := by
  change _ ≫ ((derivedCompletionRestrictionIso (algebraMap R B) a).inv.app _ ≫ _) = _
  rw [← Category.assoc, derivedCompletionRestrictionIso_inv_unit]
  exact ((derivedComplexCompletionUnit R a).naturality
    (algebraBaseChangeTensorIso R B S).hom).symm

/-- 元の G2 の H⁰ 比較は、元の二つの完備化標準単位と可換。 -/
theorem completedBaseChangeTensorH0Iso_unit :
    (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj)) ≫
      (completedBaseChangeTensorH0Iso R B S a).hom =
    (algebraBaseChangeTensorH0Iso R B S).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj) := by
  let φ := algebraMap R B
  let H := DerivedCategory.homologyFunctor (ModuleCat R) 0
  let H' := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let U := ModuleCat.restrictScalars φ
  let X := ((boundedAboveDerivedBaseChange φ).obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj
  let η := (derivedComplexCompletionUnit B (φ a)).app X
  let ρ := derivedRestrictScalarsHomologyIso φ 0
  have hc : (completedBaseChangeTensorH0Iso R B S a).hom =
      ρ.inv.app ((derivedComplexCompletionFunctor B (φ a)).obj X) ≫
        H.map (completedAlgebraBaseChangeTensorIso R B S a).hom := by
    rw [completedAlgebraBaseChangeTensorIso_eq]
    simp only [completedBaseChangeTensorH0Iso, completedBaseChangeTensorRestrictionHomologyIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  have hn := ρ.inv.naturality η
  change U.map (H'.map η) ≫ ρ.inv.app ((derivedComplexCompletionFunctor B (φ a)).obj X) =
    ρ.inv.app X ≫ H.map ((derivedRestrictScalars φ).map η) at hn
  rw [hc, ← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    completedAlgebraBaseChangeTensorIso_unit, Functor.map_comp, ← Category.assoc]
  rfl

/-- 単位可換式を元の B 上の全ての H⁰ の元で表したもの。 -/
theorem completedBaseChangeTensorH0Iso_unit_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) :
    (completedBaseChangeTensorH0Iso R B S a).hom
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) x) =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj)
        ((algebraBaseChangeTensorH0Iso R B S).hom x) :=
  congrArg (fun k => k.hom x) (completedBaseChangeTensorH0Iso_unit R B S a)

end SerrePositivity.DerivedCompletion
