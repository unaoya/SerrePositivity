module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRestrictionEqualityIso

/-!
概要：底射の等式による平方零同型の逆も、元の底変更の二射影を保持する。
方針：等式を除去し、元の係数恒等射を計算する。
規約：底射を選び直さない。使われ方：二 ImageWitness 表示から零底への移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} {f g : A ⟶ B}
  (h : f = g) (N : Bimod B B)

lemma restrictionEqualityIso_inv_projection : (restrictionEqualityIso h N).inv ≫
    projection _ _ = projection _ _ := by
  subst g
  change coefficientMap A (𝟙 (bimoduleRestrict f N)) ≫ projection _ _ = _
  rw [coefficientMap_id, Category.id_comp]

lemma restrictionEqualityIso_inv_map : (restrictionEqualityIso h N).inv ≫ baseChangeMap f N =
    baseChangeMap g N := by
  subst g
  change coefficientMap A (𝟙 (bimoduleRestrict f N)) ≫ baseChangeMap f N = _
  rw [coefficientMap_id, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
