module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCalculation
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification

/-! # 中間比較のモデル計算を既存の出力側導来制限へ移す -/
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

local notation "S" => BimoduleCategory.of A B E
  (compose A B D E (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
    (BimoduleCategory.underlying A D E R.obj))
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- source表示と実際の中間比較を続ける経路は、通常の計算射を出力で制限する経路に一致する。 -/
lemma derivedMiddleRestrictionComparison_output_restriction :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map
        ((middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
          derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  have h := derivedMiddleRestrictionComparison_calculation A B C D E F hE P Q R q hq
  have hh := congrArg (fun k =>
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫ (RG).map k) h
  exact hh.trans ((middleRightRestrictionDerivedIso A B K G E).hom.naturality
    (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)).symm

/-- 同じ表示移送を、source計算・中間比較・target計算の各像に分けた式。 -/
lemma derivedMiddleRestrictionComparison_output_restriction_expanded :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      (RG).map (derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq) ≫
      (RG).map (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    derivedMiddleRestrictionComparison_output_restriction A B C D E F K G hE P Q R q hq

end SerrePositivity.DifferentialGraded.BimoduleTensor
