module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionEqualityIso
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessCoefficient

/-!
概要：等しい底射に沿う平方零底変更を、両射影を保つ実同型で比較する。
方針：係数の恒等 underlying 同型を使い、底射の等式を除去して射影を計算する。
規約：元の係数と二つの底変更射を保持。使われ方：因子分解の係数表示の正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} {f g : A ⟶ B}
  (h : f = g) (N : Bimod B B)

def restrictionEqualityIso : algebra A (bimoduleRestrict f N) ≅
    algebra A (bimoduleRestrict g N) := coefficientIso A (bimoduleRestrictBaseEqIso h N)

lemma restrictionEqualityIso_projection : (restrictionEqualityIso h N).hom ≫
    projection _ _ = projection _ _ := coefficientMap_projection _ _

lemma restrictionEqualityIso_map : (restrictionEqualityIso h N).hom ≫ baseChangeMap g N =
    baseChangeMap f N := by
  subst g
  change coefficientMap A (𝟙 (bimoduleRestrict f N)) ≫ baseChangeMap f N = _
  rw [coefficientMap_id, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
