module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardZeroLeg

/-!
概要：元のHom–Totの第0行は、同じ標準零行射影への後合成。
方針：指定された二つの射影を各内部次数で展開する。
規約：IS-W2 C01の既存構成の評価・合成則。任意の複体射を保つ。
使われ方：HA 1.2.4、native Tot錐の標準脚の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のHom–Tot比較の第0行は、元の射と指定零行射影の合成。 -/
theorem homTotalComponent_zero_ofHom (P : Complex A) (X : CosimplicialObject (Complex A))
    (f : P ⟶ (productTotalFunctor A).obj X) :
    homTotalComponent P X 0 0 (Cochain.ofHom f) =
      Cochain.ofHom (f ≫ standardZeroLeg A X) := by
  apply Cochain.ext₀
  intro i
  simp only [homTotalComponent, Cochain.ofHom, Cochain.ofHoms, Cochain.mk, Cochain.v,
    standardZeroLeg, SerrePositivity.HomologicalAlgebra.ProductTotal.zeroRowHom,
    HomologicalComplex.comp_f, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [eqToHom_refl, Category.comp_id]
  have H : ∀ (k : ℤ) (hk : k = i),
      (f.f i ≫ eqToHom (congrArg (fun q => ((productTotalFunctor A).obj X).X q) hk.symm)) ≫
        SerrePositivity.HomologicalAlgebra.ProductTotal.π ((doubleComplexFunctor A).obj X)
          0 i k (by omega) ≫ (rowIso X 0).hom.f i =
      f.f i ≫ SerrePositivity.HomologicalAlgebra.ProductTotal.π
        ((doubleComplexFunctor A).obj X) 0 i i (by omega) ≫ (rowIso X 0).hom.f i := by
    intro k hk
    subst k
    simp only [eqToHom_refl, Category.comp_id]
  exact H (i + 0) (add_zero i)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
