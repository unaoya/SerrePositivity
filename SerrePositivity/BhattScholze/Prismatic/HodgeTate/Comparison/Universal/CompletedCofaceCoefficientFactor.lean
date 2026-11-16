module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardCompletedModelComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialComparison

/-!
# 元の完備行の係数比較と元の通常係数比較

## 概要
元の通常Tot比較と行の完備化単位からなる射を、係数射の後の同じ単位へ移す。

## 方針
各項恒等の余面比較と元の完備化単位の自然性を使う。

## 規約
元の通常Tot比較の定義を保持する。

## 使われ方
HT04.R2の指定完備終域同型と通常係数表示の照合。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalAlgebra DerivedCompletion HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 元の各項の有限完備化単位。 -/
def cosimplicialFiniteCompletionUnit {s : ℕ} (y : Fin s → B)
    (X : CosimplicialObject (Complex B)) : X ⟶ X ⋙ finiteCompletionFunctor y where
  app n := finiteCompletionUnit y (X.obj n)
  naturality _ _ g := finiteCompletionUnit_naturality y (X.map g)

/-- 元の各項の単位は同じ係数射と自然。 -/
theorem cosimplicialFiniteCompletionUnit_naturality {s : ℕ} (y : Fin s → B)
    {X Y : CosimplicialObject (Complex B)} (g : X ⟶ Y) :
    cosimplicialFiniteCompletionUnit y X ≫ Functor.whiskerRight g (finiteCompletionFunctor y) =
      g ≫ cosimplicialFiniteCompletionUnit y Y := by
  apply NatTrans.ext
  funext n
  exact (finiteCompletionUnit_naturality y (g.app n)).symm

/-- 元の行の完備化単位は各項恒等の余面比較と可換。 -/
theorem finiteCompletionRowsUnit_coface (f : A →+* B) {s : ℕ} (y : Fin s → B)
    (X : CosimplicialObject (Complex A)) :
    let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
    finiteCompletionRowsUnit y ((E.mapHomologicalComplex (.up ℕ)).obj
      ((alternatingCofaceMapComplex (Complex A)).obj X)) ≫
      ((alternatingCofaceFunctorIso (E ⋙ finiteCompletionFunctor y)).app X).hom =
    ((alternatingCofaceFunctorIso E).app X).hom ≫
      (alternatingCofaceMapComplex (Complex B)).map
        (cosimplicialFiniteCompletionUnit y (X ⋙ E)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change finiteCompletionUnit y _ ≫ 𝟙 _ = 𝟙 _ ≫ finiteCompletionUnit y _
  simp only [Category.comp_id, Category.id_comp]

/-- 元の完備行への係数比較は、元の通常係数射とその終域の標準単位に分解する。 -/
theorem baseChangeModelToCompletedCoefficientRows (f : A →+* B) {s : ℕ} (x : Fin s → A)
    (X : CosimplicialObject (Complex A)) (Y : CosimplicialObject (Complex B))
    (g : X ⋙ (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⟶ Y) :
    let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
    let C := finiteCompletionFunctor (fun j => f (x j))
    let T := cochainProductTotalizationFunctor (ModuleCat.{u} B)
    let AS := alternatingCofaceMapComplex (Complex B)
    baseChangeModelToCompletedRows f x ((alternatingCofaceMapComplex (Complex A)).obj X) (𝟙 _) ≫
      T.map ((alternatingCofaceFunctorIso (E ⋙ C)).app X).hom ≫
      T.map (AS.map (Functor.whiskerRight g C)) =
    baseChangeTotalComparison f ((alternatingCofaceMapComplex (Complex A)).obj X) ≫
      T.map ((alternatingCofaceFunctorIso E).app X).hom ≫ T.map (AS.map g) ≫
      T.map (AS.map (cosimplicialFiniteCompletionUnit (fun j => f (x j)) Y)) := by
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  let T := cochainProductTotalizationFunctor (ModuleCat.{u} B)
  let AS := alternatingCofaceMapComplex (Complex B)
  have hc := congrArg T.map (finiteCompletionRowsUnit_coface f (fun j => f (x j)) X)
  simp only [Functor.map_comp] at hc
  have hn := congrArg (fun q => T.map (AS.map q))
    (cosimplicialFiniteCompletionUnit_naturality (fun j => f (x j)) g)
  simp only [Functor.map_comp] at hn
  simp only [baseChangeModelToCompletedRows, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [← Category.assoc (T.map (finiteCompletionRowsUnit _ _)), hc]
  simp only [Category.assoc]
  rw [hn]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
