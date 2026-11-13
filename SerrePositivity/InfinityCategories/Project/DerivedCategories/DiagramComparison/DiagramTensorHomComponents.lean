module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv

/-!
概要：図式tensor–Hom同値の逆射を各点・各斉次tensorで評価する。
方針：元の図式Hom族の評価と閉tensor逆転置の成分則を使う。
規約：全次数とKoszul符号を保持する既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02の指定AW射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped TensorProduct
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
variable (P Q : J ⥤ Complex A) (T : Complex A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 同じ図式Homの逆転置は各点で元のtensor–Hom逆転置となる。 -/
theorem diagramTensorLinearHomEquiv_symm_app
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J) :
    ((diagramTensorLinearHomEquiv P Q T).symm f).app j =
      (tensorHomEquiv (P.obj j) T (Q.obj j)).symm
        ((diagramHomFamilyOfHom P Q T f).val j) := rfl

/-- 同じ逆転置の各点の斉次tensor成分。 -/
theorem diagramTensorLinearHomEquiv_symm_component
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J)
    (i q n : ℤ) (hn : i + q = n) (y : (P.obj j).X i) (x : T.X q) :
    (((diagramTensorLinearHomEquiv P Q T).symm f).app j).f n
      (HomologicalComplex.ιTensorObj (P.obj j) T i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow • (diagramCochainAt P Q (f.f q x) j).v i n hn y := by
  rw [diagramTensorLinearHomEquiv_symm_app]
  exact tensorHomEquiv_symm_component (P.obj j) T (Q.obj j)
    ((diagramHomFamilyOfHom P Q T f).val j) i q n hn y x

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
