module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeLift
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver

/-!
概要：係数射の制限と元の平方零代数の底変更を、厳密な可換式で比較する。
方針：同じ底射と元の係数射の対角直和を二つの射影で照合する。
規約：係数射の作用保存を保持。使われ方：引き戻した class 自然性の始点の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {P A B : Mon (Complex R)} (b : P ⟶ A) (f : A ⟶ B)
  (M : Bimod A A) (N : Bimod B B) (m : M ⟶ bimoduleRestrict f N)

lemma restrictionCoefficient_baseChange :
    coefficientMap P (bimoduleRestrictOver b (b ≫ f) f rfl m) ≫ baseChangeMap (b ≫ f) N =
      baseChangeMap b M ≫ mapOver f M N m := by
  apply Mon.Hom.ext
  change biprod.map (𝟙 P.X) (bimoduleRestrictOver b (b ≫ f) f rfl m).hom ≫
    biprod.map (b.hom ≫ f.hom) (𝟙 N.X) =
      biprod.map b.hom (𝟙 M.X) ≫ biprod.map f.hom m.hom
  rw [bimoduleRestrictOver_hom]
  let t : M.X ⟶ N.X := m.hom
  change biprod.map (𝟙 P.X) t ≫ biprod.map (b.hom ≫ f.hom) (𝟙 N.X) =
    biprod.map b.hom (𝟙 M.X) ≫ biprod.map f.hom t
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
