module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalDifferential
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：Hom–Tot の横微分を、元の交代余面複体の微分と同定する。
方針：零延長の指定行同型を通して横微分を戻し、同じ Hom 成分に後合成する。
規約：非負の全行を扱い、次数零の消滅と合わせて横微分全体を決める。
使われ方：HA 1.2.4、G10 の Hom–Tot 比較の鎖写像条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CochainComplex HomComplex
open AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 全ての非負行で、横微分は元の交代余面複体の微分を保つ。 -/
theorem rowDifferential (X : CosimplicialObject (Complex A)) (n m : ℕ) :
    ((doubleComplexFunctor A).obj X).d n m ≫ (rowIso X m).hom =
      (rowIso X n).hom ≫ ((alternatingCofaceMapComplex (Complex A)).obj X).d n m := by
  change (((alternatingCofaceMapComplex (Complex A)).obj X).extend
    ComplexShape.embeddingUpNat).d (n : ℤ) (m : ℤ) ≫ _ = _
  rw [HomologicalComplex.extend_d_eq ((alternatingCofaceMapComplex (Complex A)).obj X)
    ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
    (j := m) (j' := (m : ℤ)) rfl]
  simp [rowIso]

/-- 正の行の Hom 横微分は、一つ前の指定成分への交代余面微分の後合成。 -/
theorem homTotalHorizontalTerm_succ_v (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (n : ℕ) (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (i j : ℤ) (hij : i + (p + 1 - (n + 1 : ℕ)) = j) :
    (homTotalHorizontalTerm P X p (n + 1) f).v i j hij =
      (homTotalComponent P X p n f).v i j (by omega) ≫
        (((alternatingCofaceMapComplex (Complex A)).obj X).d n (n + 1)).f j := by
  have hn : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  have hd := congrArg (fun g => g.f j) (rowDifferential X n (n + 1))
  simp only [HomologicalComplex.comp_f] at hd
  have haux (a : ℤ) (ha : a = (n : ℤ)) (haj : a + j = i + p) :
      f.v i (i + p) rfl ≫ SerrePositivity.HomologicalAlgebra.ProductTotal.π
        ((doubleComplexFunctor A).obj X) a j (i + p) haj ≫
        (((doubleComplexFunctor A).obj X).d a (n + 1 : ℕ)).f j ≫
        (rowIso X (n + 1)).hom.f j =
      (homTotalComponent P X p n f).v i j (by omega) ≫
        (((alternatingCofaceMapComplex (Complex A)).obj X).d n (n + 1)).f j := by
    subst a
    rw [hd]
    rfl
  exact haux _ hn (by omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
