module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomology

/-!
概要：複体ホモロジーと明示的隣接短複体のホモロジーの比較の自然性。
方針：隣接短複体への自然同型にホモロジー関手を適用する。
規約：全整数次数の実鎖写像を扱う。
使われ方：直和ホモロジー比較と係数射の可換性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {K L : Complex R}

@[reassoc]
lemma dgComplexHomologyIsoSc_naturality (f : K ⟶ L) (q : ℤ) :
    HomologicalComplex.homologyMap f q ≫
      (L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom =
    (K.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
          (q - 1) q (q + 1)).map f) := by
  exact (Functor.isoWhiskerRight
    (HomologicalComplex.natIsoSc' (ModuleCat R) (.up ℤ)
      (q - 1) q (q + 1) (by simp) (by simp))
    (ShortComplex.homologyFunctor (ModuleCat R))).hom.naturality f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
