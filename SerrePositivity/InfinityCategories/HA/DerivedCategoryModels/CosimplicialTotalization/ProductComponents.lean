module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductTotal
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：余単体的積全複体の標準成分への射影と、図式の射についての自然性。
方針：整数への零延長の指定同型を使い、二重複体の射影を元の余単体次数へ戻す。
規約：次数 q の n 成分は Xⁿ の次数 q−n。これは次数ごとの射であり、Xⁿ への鎖写像ではない。
使われ方：HA 1.2.4、G10 の標準脚・射・全関手の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 零延長後の非負横次数の行を、元の余単体的複体へ戻す指定同型。 -/
def rowIso (X : CosimplicialObject (Complex A)) (n : ℕ) :
    ((doubleComplexFunctor A).obj X).X (n : ℤ) ≅ X.obj ⦋n⦌ :=
  ((alternatingCofaceMapComplex (Complex A)).obj X).extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl

/-- 全次数 q の指定 n 成分への射影。 -/
def componentπ (X : CosimplicialObject (Complex A)) (n : ℕ) (q : ℤ) :
    ((productTotalFunctor A).obj X).X q ⟶ (X.obj ⦋n⦌).X (q-n) :=
  SerrePositivity.HomologicalAlgebra.ProductTotal.π
    ((doubleComplexFunctor A).obj X) n (q-n) q (by omega) ≫
      (rowIso X n).hom.f (q-n)

/-- 非負横次数の指定同型は元の図式の射と可換。 -/
@[reassoc]
theorem rowIso_naturality {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) (n : ℕ) :
    (((doubleComplexFunctor A).map f).f n) ≫ (rowIso Y n).hom =
      (rowIso X n).hom ≫ f.app ⦋n⦌ := by
  change (HomologicalComplex.extendMap ((alternatingCofaceMapComplex (Complex A)).map f)
    ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f
    ((alternatingCofaceMapComplex (Complex A)).map f) ComplexShape.embeddingUpNat
    (i := n) (i' := (n : ℤ)) rfl]
  simp [rowIso]

/-- 同じ積 total 関手の射は、各元の余単体成分への射影と厳密に可換。 -/
@[reassoc]
theorem componentπ_naturality {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    (n : ℕ) (q : ℤ) :
    ((productTotalFunctor A).map f).f q ≫ componentπ Y n q =
      componentπ X n q ≫ (f.app ⦋n⦌).f (q-n) := by
  dsimp only [componentπ, productTotalFunctor, Functor.comp_map]
  rw [← Category.assoc, SerrePositivity.HomologicalAlgebra.ProductTotal.map_π,
    Category.assoc]
  rw [← HomologicalComplex.comp_f, rowIso_naturality, HomologicalComplex.comp_f]
  rfl

/-- 零延長で入れた負の行は零複体。 -/
theorem negativeRow_isZero (X : CosimplicialObject (Complex A)) (a : ℤ) (ha : a < 0) :
    Limits.IsZero (((doubleComplexFunctor A).obj X).X a) :=
  ((alternatingCofaceMapComplex (Complex A)).obj X).isZero_extend_X
    ComplexShape.embeddingUpNat a (fun n hn => by change (n : ℤ) = a at hn; omega)

/-- 元の非負余単体次数の成分だけで、積全複体への次数ごとの射を判定できる。 -/
theorem component_hom_ext (X : CosimplicialObject (Complex A)) {M : ModuleCat.{u} A} (q : ℤ)
    {f g : M ⟶ ((productTotalFunctor A).obj X).X q}
    (h : ∀ n, f ≫ componentπ X n q = g ≫ componentπ X n q) : f = g := by
  apply SerrePositivity.HomologicalAlgebra.ProductTotal.hom_ext
    ((doubleComplexFunctor A).obj X) q
  intro a b hab
  by_cases ha : 0 ≤ a
  · lift a to ℕ using ha
    have hb : b = q - (a : ℤ) := by omega
    subst b
    apply (cancel_mono ((rowIso X a).hom.f (q-a))).mp
    simpa only [componentπ, Category.assoc] using h a
  · exact ((HomologicalComplex.eval _ _ b).map_isZero
      (negativeRow_isZero X a (by omega))).eq_of_tgt _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
