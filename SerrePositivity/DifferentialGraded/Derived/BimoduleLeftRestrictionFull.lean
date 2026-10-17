module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFamily
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLift

/-! # 外側の左dg作用の制限と両変数の全導来合成の自然同型 -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)

/-- 合成後に出力の外側左作用を制限する、既存の全導来関手族。 -/
def leftRestrictionDerivedComposeSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 後因子の外側左作用を制限してから合成する、既存の全導来関手族。 -/
def leftRestrictionDerivedComposeTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedBimoduleRestriction A C D C E (DGFunctor.id C) F ⋙
    derivedBimoduleComposeFunctor A B C D hD

/-- sourceは右K-flatモデル上で既存の固定因子関手族になる。 -/
def leftRestrictionDerivedComposeSourceBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        leftRestrictionDerivedComposeSource A B C E D F hE ≅
      leftRestrictionKFlatComposeTarget A B C E D F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE B)
    ((whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F))

/-- targetは右K-flat性を保つ直接制限による固定因子関手族になる。 -/
def leftRestrictionDerivedComposeTargetBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        leftRestrictionDerivedComposeTarget A B C E D F hD ≅
      leftRestrictionKFlatComposeSource A B C E D F :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (rightKFlatInclusion A C E)
        (middleLeftRestrictionDerivedIso A C E D F).symm)
      (derivedBimoduleComposeFunctor A B C D hD) ≪≫
    Functor.isoWhiskerLeft (rightKFlatLeftRestriction A C E D F)
      (rightKFlatComposePresentationIso A C D hD B)

/-- 外側の左dg作用の制限は、両変数の全導来合成と自然に可換する。 -/
def derivedBimoduleComposeLeftRestrictionIso :
    leftRestrictionDerivedComposeSource A B C E D F hE ≅
      leftRestrictionDerivedComposeTarget A B C E D F hD :=
  rightKFlatDerivedIsoOfPrecomp A C E hE _ _
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE ≪≫
      (leftRestrictionKFlatComposeIso A B C E D F).symm ≪≫
        (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
