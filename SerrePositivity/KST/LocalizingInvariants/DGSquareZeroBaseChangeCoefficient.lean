module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangePullback
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap

/-!
概要：元の底上の係数射の平方零代数射は、係数の底制限を通って因子分解する。
方針：底変更の恒等係数射と直和射の二座標を計算する。
規約：元の mapOver を厳密に回収。使われ方：共通底の Postnikov class の係数像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B)
  (M : Bimod A A) (N : Bimod B B) (t : M ⟶ bimoduleRestrict q N)

lemma coefficientMap_baseChangeMap : coefficientMap A t ≫ baseChangeMap q N = mapOver q M N t := by
  apply Mon.Hom.ext
  let c : M.X ⟶ N.X := t.hom
  change biprod.map (𝟙 A.X) c ≫ biprod.map q.hom (𝟙 N.X) = biprod.map q.hom c
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
