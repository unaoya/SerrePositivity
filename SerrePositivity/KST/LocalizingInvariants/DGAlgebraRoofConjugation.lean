module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof

/-!
概要：実比較射・指定 roof・準同型の逆を合成した roof の、元の実射影を供給する。
方針：二つの実 pullback の射影を保持し、元の分母と分子の厳密な式を取り出す。
規約：評価後の等式で代用しない。使われ方：実乗法的三角形の正方形移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation
variable (R : Type u) [CommRing R] {A B A' B' : Mon (Complex R)}
  (r : SurjectiveRoof R B' A') (b : B ⟶ B') (a : A ⟶ A') (ha : QuasiIso a.hom)

abbrev firstRoof := SurjectiveRoof.comp R (SurjectiveRoof.ofHom R b) r
abbrev inverseRoof := SurjectiveRoof.ofQuasiIsoInverse R a ha

def roof : SurjectiveRoof R B A := SurjectiveRoof.comp R (firstRoof R r b) (inverseRoof R a ha)

def source : (roof R r b a ha).apex ⟶ r.apex :=
  MonoidPullback.fst (firstRoof R r b).numerator (MappingPath.target R a) ≫
    MonoidPullback.snd b r.denominator

def leftPath : (roof R r b a ha).apex ⟶ MappingPath.algebra R a :=
  MonoidPullback.snd (firstRoof R r b).numerator (MappingPath.target R a)

lemma source_denominator : source R r b a ha ≫ r.denominator =
    (roof R r b a ha).denominator ≫ b := by
  change (_ ≫ MonoidPullback.snd b r.denominator) ≫ r.denominator =
    (_ ≫ (MonoidPullback.fst b r.denominator ≫ 𝟙 B)) ≫ b
  rw [Category.comp_id, Category.assoc, ← MonoidPullback.condition, ← Category.assoc]
  rfl

lemma source_numerator : source R r b a ha ≫ r.numerator =
    leftPath R r b a ha ≫ MappingPath.target R a := by
  change (_ ≫ MonoidPullback.snd b r.denominator) ≫ r.numerator = _
  rw [Category.assoc]
  exact MonoidPullback.condition _ _

lemma numerator_eq : (roof R r b a ha).numerator =
    leftPath R r b a ha ≫ MappingPath.projection R a := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation
