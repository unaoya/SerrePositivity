module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugation

/-!
概要：元の分母・分子に厳密に整合する持ち上げを、正方形移送した実 roof に移す。
方針：元の二つの pullback に持ち上げ、左比較の MappingPath の切断を使う。
規約：元の両脚の厳密な等式を保持。使われ方：cell 細分後の左三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation
variable (R : Type u) [CommRing R] {A B A' B' W : Mon (Complex R)}
  (r : SurjectiveRoof R B' A') (b : B ⟶ B') (a : A ⟶ A') (ha : QuasiIso a.hom)
  (l : W ⟶ r.apex) (z : W ⟶ B) (x : W ⟶ A)
  (hl : l ≫ r.denominator = z ≫ b) (hx : l ≫ r.numerator = x ≫ a)

abbrev firstLift : W ⟶ (firstRoof R r b).apex := MonoidPullback.lift b r.denominator z l hl.symm

include hx in
lemma lift_condition : firstLift R r b l z hl ≫ (firstRoof R r b).numerator =
    (x ≫ MappingPath.section_ R a) ≫ MappingPath.target R a := by
  change MonoidPullback.lift b r.denominator z l hl.symm ≫
    (MonoidPullback.snd b r.denominator ≫ r.numerator) = _
  rw [← Category.assoc, MonoidPullback.lift_snd, hx, Category.assoc, MappingPath.section_target]

def lift : W ⟶ (roof R r b a ha).apex :=
  MonoidPullback.lift (firstRoof R r b).numerator (MappingPath.target R a)
    (firstLift R r b l z hl) (x ≫ MappingPath.section_ R a) (lift_condition R r b a l z x hl hx)

lemma lift_denominator : lift R r b a ha l z x hl hx ≫ (roof R r b a ha).denominator = z := by
  change MonoidPullback.lift _ _ _ _ _ ≫
    (MonoidPullback.fst _ _ ≫ (MonoidPullback.fst b r.denominator ≫ 𝟙 B)) = z
  rw [← Category.assoc, MonoidPullback.lift_fst, ← Category.assoc,
    MonoidPullback.lift_fst, Category.comp_id]

lemma lift_numerator : lift R r b a ha l z x hl hx ≫ (roof R r b a ha).numerator = x := by
  change MonoidPullback.lift _ _ _ _ _ ≫ (MonoidPullback.snd _ _ ≫ MappingPath.projection R a) = x
  rw [← Category.assoc, MonoidPullback.lift_snd, Category.assoc,
    MappingPath.section_projection, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation
