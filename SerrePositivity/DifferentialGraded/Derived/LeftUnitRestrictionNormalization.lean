module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionSourceNormalization
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionModelCalculation
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionModel

/-! # 対角を代入した全導来左単位経路のモデル正規化 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [dgB : DGCategory A B] [smallB : Small.{u} B]
  (D : Type w) [dgD : DGCategory A D] [smallD : Small.{u} D]
  (C : Type z) [dgC : DGCategory A C] [smallC : Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C) (Q : RightKFlatBimoduleCategory A B C)
  (R : RightKFlatBimoduleCategory A D C)

local notation "DB" => BimoduleCategory.of A B B (Bimodule.diagonal A B)
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F) DB
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 一般のモデルprefixを対角の左制限に特殊化した、既存比較の射。 -/
def leftUnitRestrictedModelPrefix := fun q hq =>
  restrictedMiddleModelPrefix A B B D C F D F hC DB Q R q hq

/-- 指定モデル上で、対角射と外側・中間比較に左単位子を続けた実際の経路。 -/
def leftUnitRestrictionModelPath := fun q hq =>
  (derivedComposeWith A D D C R.obj R.property).map
      ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F)) ≫
    leftUnitRestrictedModelPrefix A B D C F hC Q R q hq ≫
    (RR).map
      ((middleDerivedSourceFamilyIdentification A B B D C F hC Q).hom.app DB ≫
        ((derivedMiddleRestrictionNatTrans A B B D C F hC).app
          ((bimoduleToDerived A B C).obj Q.obj)).app ((bimoduleToDerived A B B).obj DB) ≫
        (derivedBimoduleComposeKFlatValueIso A B B C hC Q DB).hom) ≫
    (RR).map ((bimoduleToDerived A B C).map ((leftUnitNatIso A B C).hom.app Q.obj))

private lemma paste_unit_square {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d e : W} {x y : V} (p : a ⟶ b) (m : b ⟶ H.obj x)
    (f : x ⟶ y) (r : b ⟶ c) (s : c ⟶ d) (u : d ⟶ H.obj x)
    (v : d ⟶ e) (w : e ⟶ H.obj y) (t : a ⟶ e)
    (h₁ : m = r ≫ s ≫ u) (h₂ : u ≫ H.map f = v ≫ w) (h₃ : p ≫ r ≫ s ≫ v = t) :
    p ≫ m ≫ H.map f = t ≫ w := by
  rw [h₁]
  simp only [Category.assoc]
  rw [h₂]
  exact (by simpa only [Category.assoc] using congrArg (fun k => k ≫ w) h₃)

/-- 対角での組合せのモデル計算は、Rの左単位子に増大射を続けた射に一致する。 -/
lemma leftUnitRestrictionModelPath_eq (q : _) (hq : _) :
    leftUnitRestrictionModelPath A B D C F hC Q R q hq =
      (bimoduleToDerived A D C).map ((leftUnitNatIso A D C).hom.app R.obj) ≫
      (bimoduleToDerived A D C).map q ≫
      (middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj := by
  let U := (composeWith A B B C Q.obj).obj DB
  let f : U ⟶ Q.obj := (leftUnitNatIso A B C).hom.app Q.obj
  have hm := derivedBimoduleRestriction_model_calculation A B B D C F D F hC DB Q R q hq
  have hn := (middleRightRestrictionDerivedIso A B D F C).hom.naturality f
  have hu := leftUnitRestriction_localized_augmentation A B D C F Q.obj R.obj q
  unfold leftUnitRestrictionModelPath
  rw [derivedComposeWith_map_base]
  have result := paste_unit_square (RR)
    ((bimoduleToDerived A D C).map
      (composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 R.obj)))
    _ ((bimoduleToDerived A B C).map f) _ _ _ _ _ _ hm hn.symm hu
  convert result using 1 <;>
    first | rfl | simp only [leftUnitRestrictedModelPrefix, f, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
