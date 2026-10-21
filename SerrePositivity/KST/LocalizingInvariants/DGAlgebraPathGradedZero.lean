module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeZeroLift

/-!
概要：比較 cochain を零とする斉次経路と、両端・対角・経路射との整合。
方針：mapping cocone の次数零包含と、実射の成分式を使う。
規約：この斉次切断に微分保存は要求しない。使われ方：相対経路の各次数全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R]

def gradedZero (B : Mon (Complex R)) (n : ℤ) : (B.X ⊞ B.X).X n ⟶ (algebra R B).X.X n :=
  (mappingCocone.inl (difference R B)).v n n (add_zero n)

lemma gradedZero_source (B : Mon (Complex R)) (n : ℤ) :
    gradedZero R B n ≫ (source R B).hom.f n = (biprod.fst : B.X ⊞ B.X ⟶ B.X).f n := by
  change (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
    ((mappingCocone.fst (difference R B)).f n ≫ (biprod.fst : B.X ⊞ B.X ⟶ B.X).f n) = _
  rw [← Category.assoc, mappingCocone.inl_v_fst_f, Category.id_comp]

lemma gradedZero_target (B : Mon (Complex R)) (n : ℤ) :
    gradedZero R B n ≫ (target R B).hom.f n = (biprod.snd : B.X ⊞ B.X ⟶ B.X).f n := by
  change (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
    ((mappingCocone.fst (difference R B)).f n ≫ (biprod.snd : B.X ⊞ B.X ⟶ B.X).f n) = _
  rw [← Category.assoc, mappingCocone.inl_v_fst_f, Category.id_comp]

lemma gradedZero_map {A B : Mon (Complex R)} (f : A ⟶ B) (n : ℤ) :
    gradedZero R A n ≫ (map R f).hom.f n =
      (biprod.map f.hom f.hom).f n ≫ gradedZero R B n :=
  cochainMappingCoconeMap_inl (difference R A) (difference R B)
    (biprod.map f.hom f.hom) f.hom (difference_naturality R f) n

lemma gradedZero_diagonal (B : Mon (Complex R)) (n : ℤ) :
    (biprod.lift (𝟙 B.X) (𝟙 B.X)).f n ≫ gradedZero R B n = (diagonal R B).hom.f n :=
  (cochainMappingCocone_lift_zero_f (difference R B)
    (biprod.lift (𝟙 B.X) (𝟙 B.X)) (diagonal_boundary R B) n).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
