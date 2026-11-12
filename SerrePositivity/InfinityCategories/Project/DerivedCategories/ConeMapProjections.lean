module
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # 可換四角形による cone 射の二射影

概要：cone 射は二つの直和射影と厳密に可換である。
方針：cone の二包含で射を比較し、desc の評価公式を使う。
規約：cochain 次数 +1 と 0 の射影。使われ方：D7 の回転比較の座標計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C D : Complex S}

/-- Cone 射の第一座標は始域側の鎖写像による座標の像。 -/
lemma coneMap_f_fst_v (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (h : f ≫ b = a ≫ g) (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.map f g a b h).f p ≫ (mappingCone.fst g).val.v p q hpq =
      (mappingCone.fst f).val.v p q hpq ≫ a.f q := by
  apply mappingCone.ext_from f q p hpq
  · simp [mappingCone.map, Category.assoc]
  · simp [mappingCone.map, Category.assoc]

/-- Cone 射の第二座標は終域側の鎖写像による座標の像。 -/
lemma coneMap_f_snd_v (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (h : f ≫ b = a ≫ g) (p : ℤ) :
    (mappingCone.map f g a b h).f p ≫ (mappingCone.snd g).v p p (add_zero p) =
      (mappingCone.snd f).v p p (add_zero p) ≫ b.f p := by
  apply mappingCone.ext_from f (p + 1) p rfl
  · simp [mappingCone.map, Category.assoc]
  · simp [mappingCone.map, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
