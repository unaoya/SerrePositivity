module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # 複体の射の可換式の斉次元での評価 -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma chain_comp_apply {X Y Z : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℤ) (x : X.X n) : (f ≫ g).f n x = g.f n (f.f n x) := rfl

/-- 合成の等式を、各複体の内部構成を展開せずに斉次元へ適用する。 -/
lemma chain_comp_apply_of_eq {X Y Z : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (n : ℤ) (x : X.X n) : g.f n (f.f n x) = h.f n x :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom w n) x

/-- 各次数の元での等式から複体の射の等式を得る。 -/
lemma chain_ext_apply {X Y : Complex A} (f g : X ⟶ Y)
    (h : ∀ (n : ℤ) (x : X.X n), f.f n x = g.f n x) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h n

end SerrePositivity.DifferentialGraded
