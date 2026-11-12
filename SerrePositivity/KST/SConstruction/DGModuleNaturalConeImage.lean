module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImageInput
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeDesc
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv

/-!
概要：元実 cone の dg 関手像への同じ全厳密比較を構成する。
方針：元左包含像の微分と符号付き全自然性を cone descent へ渡す。
規約：元実 cone・元右包含・同じ実後合成を保持する。
使われ方：全実 gluing 逆回転を同じ realization へ運ぶ評価比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
  (Q : DGFunctor R (RightModule R D) (RightModule R E))
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FQ" => DGFunctor.comp F Q
local notation "GQ" => DGFunctor.comp G Q
local notation "CQ" => DGFunctor.comp (CF) Q
local notation "ηQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "νQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) Q
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "s" => dgModuleNaturalConeImageInput R E D F G η Q

/-- 概要：元左包含像の微分は同じ元右包含像の指定閉合成。
方針：元 cone image の境界式を全比較の閉成分へ回収する。
規約：元後合成射の等式。使われ方：同じ cone descent の微分入力。 -/
lemma dgModuleNaturalConeImage_boundary (x : P) :
    (moduleHom R E ((FQ).obj x) ((CQ).obj x)).d (-1) 0 (s x) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R E (FQ) (GQ) (ηQ) x ≫
          dgModuleNaturalConeArrow R E (GQ) (CQ) (νQ) x))).val := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeInl_d R D E Q (a x)).trans
    (congrArg (fun t => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) t)).val)
      (congrArg₂ (fun p q => p ≫ q)
        (dgModuleNaturalConePostcompArrow R E D F G η Q x).symm
        ((congrArg Q.onClosed.map (dgModuleNaturalConeInr_arrow R D F G η x)).symm.trans
          (dgModuleNaturalConePostcompArrow R E D G (CF) (ν) Q x).symm)))

/-- 概要：写した射の元 cone から元 cone の同じ実像への全厳密比較。
方針：元全自然な左包含像と元右包含像を同じ descent へ渡す。
規約：元全 Hom を保持。使われ方：元実逆回転の realization 全比較。 -/
def dgModuleNaturalConeImage :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgModuleNaturalConeFunctor R E (FQ) (GQ) (ηQ)) (CQ) :=
  dgModuleNaturalConeDesc R E (FQ) (GQ) (CQ) (ηQ) (νQ) (s)
    (dgModuleNaturalConeImage_boundary R E D F G η Q)
    (dgModuleNaturalConeImageInput_naturality R E D F G η Q)
end SerrePositivity.KST.SConstruction
