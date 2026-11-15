module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComponents

/-!
概要：元の余単体成分への Hom 射影と Hom 微分の両立。
方針：一般の行成分公式を零延長の指定行同型で移し、同じ component の公式を得る。
規約：横微分項は元の二重複体の微分を使用する。標準射影を選び直さない。
使われ方：HA 1.2.4、G10 の Hom と積 Tot の比較射の閉性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 元の Hom 成分は一般の行射影と指定行同型の合成そのもの。 -/
theorem homTotalComponent_eq_row (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (n : ℕ) (f : Homogeneous P ((productTotalFunctor A).obj X) p) :
    homTotalComponent P X p n f =
      (SerrePositivity.HomologicalAlgebra.ProductTotal.homRowComponent P
        ((doubleComplexFunctor A).obj X) p n f).comp
          (Cochain.ofHom (rowIso X n).hom) (add_zero _) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v]
  rfl

/-- Hom 微分の横方向の項。前の行の同じ射影と元の横微分を使う。 -/
def homTotalHorizontalTerm (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (n : ℕ) (f : Homogeneous P ((productTotalFunctor A).obj X) p) :
    Homogeneous P (X.obj ⦋n⦌) (p + 1 - n) :=
  Cochain.mk (fun i j hij => f.v i (i + p) rfl ≫
    SerrePositivity.HomologicalAlgebra.ProductTotal.π
      ((doubleComplexFunctor A).obj X) ((n : ℤ) - 1) j (i + p) (by omega) ≫
    (((doubleComplexFunctor A).obj X).d ((n : ℤ) - 1) n).f j ≫ (rowIso X n).hom.f j)

/-- 前回の指定 Hom 成分自体についての、横微分と行内 Hom 微分の公式。 -/
theorem homTotalComponent_differential (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (n : ℕ) (f : Homogeneous P ((productTotalFunctor A).obj X) p) :
    homTotalComponent P X (p + 1) n (δ p (p + 1) f) =
      homTotalHorizontalTerm P X p n f +
        (n : ℤ).negOnePow • δ (p - n) (p + 1 - n) (homTotalComponent P X p n f) := by
  rw [homTotalComponent_eq_row, homTotalComponent_eq_row, δ_comp_ofHom]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.add_v,
    Cochain.units_smul_v]
  have h := SerrePositivity.HomologicalAlgebra.ProductTotal.homRowComponent_differential_v
    P ((doubleComplexFunctor A).obj X) p n f i j hij
  have hh := congrArg (fun z => z ≫ (rowIso X n).hom.f j) h
  simpa only [add_comp, Linear.units_smul_comp, Category.assoc,
    homTotalHorizontalTerm, SerrePositivity.HomologicalAlgebra.ProductTotal.homRowComponent,
    Cochain.mk_v] using hh

/-- 余単体次数零では前の行が零なので横微分項が消える。 -/
theorem homTotalHorizontalTerm_zero (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (f : Homogeneous P ((productTotalFunctor A).obj X) p) :
    homTotalHorizontalTerm P X p 0 f = 0 := by
  apply Cochain.ext
  intro i j hij
  have hz : (((doubleComplexFunctor A).obj X).d (-1) 0).f j = 0 :=
    congrArg (fun g => g.f j) ((negativeRow_isZero X (-1) (by omega)).eq_of_src
      (((doubleComplexFunctor A).obj X).d (-1) 0) 0)
  change _ ≫ _ ≫ (((doubleComplexFunctor A).obj X).d (-1) 0).f j ≫ _ = 0
  rw [hz, zero_comp, comp_zero, comp_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
