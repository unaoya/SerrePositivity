module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedFamilies

/-! 同じ導来単体族を、元の複体パラメーターの共通宇宙表示へ移す。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingUniverseModuleDerivedSimplexFamily (A : Complex R) (n : ℕ)
    (h : (Δ[n] : SSet.{max (u + 1) v}) ⊗ complexPinchedSpace.{u, max (u + 1) v} A ⟶
      dgModuleDerivedInfinityCategory R C) :=
  ((Δ[n] : SSet.{max (u + 1) v w}) ◁
      (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} A).hom) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} n h

lemma dgGluingUniverseModuleDerivedSimplexFamily_face (A : Complex R) {n : ℕ}
    (h : (Δ[n + 1] : SSet.{max (u + 1) v}) ⊗ complexPinchedSpace.{u, max (u + 1) v} A ⟶
      dgModuleDerivedInfinityCategory R C) (i : Fin (n + 2)) :
    (SSet.stdSimplex.δ i ▷ _) ≫ dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C A
        (n + 1) h =
      dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C A n
        ((SSet.stdSimplex.δ i ▷ _) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories
