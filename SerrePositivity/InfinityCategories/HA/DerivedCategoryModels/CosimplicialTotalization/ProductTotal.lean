module

public import SerrePositivity.HomologicalAlgebra.ProductTotal
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：余単体的な非有界複体の非正規化積全複体を全関手として定める。
方針：交代余面複体の横次数を整数へ零延長し、反対圏による積 total を適用する。
規約：全次数 q の成分は n≥0 に対する Xⁿ の次数 q−n の積。
使われ方：HA 1.2.4、HTT 4.2.4.1。G10 の線形 Tot の模型。極限性は後続で示す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 余単体次数を横の非負余鎖次数とする二重複体の全関手。 -/
def doubleComplexFunctor :
    CosimplicialObject (Complex A) ⥤ HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ) :=
  alternatingCofaceMapComplex (Complex A) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (Complex A)

/-- 非有界な余単体的複体の積全複体。対象・射を同じ関手で保持する。 -/
def productTotalFunctor : CosimplicialObject (Complex A) ⥤ Complex A :=
  doubleComplexFunctor A ⋙
    SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
