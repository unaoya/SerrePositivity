module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleEquivalence

/-! # 両変数の全導来bimodule圏上の合成とK-flat因子での計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 後因子Qを外変数とする導来合成。両変数とも指定準同型の全局所化上にある。 -/
def derivedBimoduleComposeFunctor (hE : localHomKFlat A E) :
    DerivedBimoduleCategory A C E ⥤
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedRightKFlatReplacement A C E hE ⋙ rightFactorLocalizedComposeFunctor A B C E

/-- K-flat部分圏の局所化へ制限すると既存の固定因子関手族と自然同型になる。 -/
def derivedBimoduleComposeKFlatFamilyIso (hE : localHomKFlat A E) :
    rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE ≅
      rightFactorLocalizedComposeFunctor A B C E :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementUnitIso A C E hE)
      (rightFactorLocalizedComposeFunctor A B C E) ≪≫
    Functor.leftUnitor (rightFactorLocalizedComposeFunctor A B C E)

def derivedBimoduleComposeKFlatIso (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ≅
      derivedComposeWith A B C E Q.obj Q.property :=
  (derivedBimoduleComposeKFlatFamilyIso A B C E hE).app ((rightKFlatToDerived A C E).obj Q)

def derivedBimoduleComposeKFlatValueIso (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)).obj
        ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj (BimoduleCategory.of A B E
        (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q.obj))) :=
  (derivedBimoduleComposeKFlatIso A B C E hE Q).app ((bimoduleToDerived A B C).obj P)

/-- 任意の指定された右K-flat解像度で、同じ導来合成関手を計算できる。 -/
def derivedBimoduleComposeResolutionComputation (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ≅
      derivedComposeWith A B C E R.obj R.property :=
  (derivedBimoduleComposeFunctor A B C E hE).mapIso (bimoduleDerivedIso A C E q hq).symm ≪≫
    derivedBimoduleComposeKFlatIso A B C E hE R

lemma derivedBimoduleComposeKFlatIso_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) ≫
        (derivedBimoduleComposeKFlatIso A B C E hE Q').hom =
      (derivedBimoduleComposeKFlatIso A B C E hE Q).hom ≫
        derivedComposeWithMap A B C E Q.property Q'.property g.hom := by
  have h := (derivedBimoduleComposeKFlatFamilyIso A B C E hE).hom.naturality
    ((rightKFlatToDerived A C E).map g)
  change (derivedBimoduleComposeFunctor A B C E hE).map
      ((rightKFlatDerivedInclusion A C E).map ((rightKFlatToDerived A C E).map g)) ≫ _ =
    _ ≫ (rightFactorLocalizedComposeFunctor A B C E).map ((rightKFlatToDerived A C E).map g) at h
  rw [rightKFlatDerivedInclusion_map_base, rightFactorLocalizedComposeFunctor_map_base] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
