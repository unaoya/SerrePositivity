module
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-! 二つの実 Hom 閉元を、同じ複体直和の閉元へ束ねる。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable {R : Type u} [CommRing R] (P Q : Complex R) (n : ℤ) (a : P.X n) (b : Q.X n)

/-- 実包含を使う、同じ複体直和の斉次元。 -/
def dgGluingBiproductElement : (P ⊞ Q).X n :=
  (biprod.inl : P ⟶ P ⊞ Q).f n a + (biprod.inr : Q ⟶ P ⊞ Q).f n b

/-- 左射影は元の同じ元を回収。 -/
lemma dgGluingBiproductElement_fst :
    (biprod.fst : P ⊞ Q ⟶ P).f n (dgGluingBiproductElement P Q n a b) = a := by
  have hl := congrArg (fun f => f.f n a) (biprod.inl_fst (X := P) (Y := Q))
  have hr := congrArg (fun f => f.f n b) (biprod.inr_fst (X := P) (Y := Q))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    HomologicalComplex.zero_f, ModuleCat.id_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hl hr
  simp only [dgGluingBiproductElement, map_add, hl, hr, add_zero]

/-- 右射影も元の同じ元を回収。 -/
lemma dgGluingBiproductElement_snd :
    (biprod.snd : P ⊞ Q ⟶ Q).f n (dgGluingBiproductElement P Q n a b) = b := by
  have hl := congrArg (fun f => f.f n a) (biprod.inl_snd (X := P) (Y := Q))
  have hr := congrArg (fun f => f.f n b) (biprod.inr_snd (X := P) (Y := Q))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    HomologicalComplex.zero_f, ModuleCat.id_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hl hr
  simp only [dgGluingBiproductElement, map_add, hl, hr, zero_add]

/-- 両元が閉じるなら、同じ直和元も閉じる。 -/
lemma dgGluingBiproductElement_closed
    (ha : P.d n (n + 1) a = 0) (hb : Q.d n (n + 1) b = 0) :
    (P ⊞ Q).d n (n + 1) (dgGluingBiproductElement P Q n a b) = 0 := by
  have hl := congrArg (fun f => f a) ((biprod.inl : P ⟶ P ⊞ Q).comm n (n + 1))
  have hr := congrArg (fun f => f b) ((biprod.inr : Q ⟶ P ⊞ Q).comm n (n + 1))
  simp only [ModuleCat.comp_apply, ha, hb, map_zero] at hl hr
  simp only [dgGluingBiproductElement, map_add, hl, hr, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
