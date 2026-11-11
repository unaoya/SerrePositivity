module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImage
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp

/-!
概要：同じ cone image 全比較が元右包含の実像を全厳密に保持することを示す。
方針：元 descent の指定右包含回収を全閉成分へ適用する。
規約：全厳密比較の等号を保持する。
使われ方：元全実逆回転の包含二単体を realization へ運ぶ全図式比較。
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


local notation "CηQ" => dgModuleNaturalConeFunctor R E (FQ) (GQ) (ηQ)
local notation "θ" => dgModuleNaturalConeImage R E D F G η Q
local notation "ιQ" => dgModuleNaturalConeInr R E (FQ) (GQ) (ηQ)

/-- 概要：元 cone image 全比較の包含制限は元右包含の全実像そのもの。
方針：元 descent の包含式を閉成分の外延性へ渡す。
規約：全 Hom を保持する等号。使われ方：指定包含二単体の realization 比較。 -/
lemma dgModuleNaturalConeImage_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ιQ) (θ) = (νQ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply (closedHomEquiv R (RightModule R E) ((GQ).obj x) ((CQ).obj x)).symm.injective
  change dgModuleNaturalConeArrow R E (GQ) (CQ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ιQ) (θ)) x =
    dgModuleNaturalConeArrow R E (GQ) (CQ) (νQ) x
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeInr_arrow]
  exact dgModuleNaturalConeDesc_inr R E (FQ) (GQ) (CQ) (ηQ) (νQ) (s)
    (dgModuleNaturalConeImage_boundary R E D F G η Q)
    (dgModuleNaturalConeImageInput_naturality R E D F G η Q) x
end SerrePositivity.KST.SConstruction
