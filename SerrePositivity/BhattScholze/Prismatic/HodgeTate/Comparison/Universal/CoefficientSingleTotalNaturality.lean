module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel

/-!
# 離散係数行の指定Tot同型の自然性

## 概要
元の各射影で指定したTot同型は、元の係数図式の任意の線形射と可換となる。

## 方針
交代余面複体、零延長とsingleの同型、縦零次の射影の三つの自然性を合成する。

## 規約
対象ごとにホモロジー同型を選び直さない。

## 使われ方
元の通常被覆係数射を、元の剰余係数複体の射へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の係数行をsingleへ置くTot同型は、同じ係数行の射について自然。 -/
@[reassoc] theorem coefficientSingleTotalIso_naturality
    {M N : CosimplicialObject (ModuleCat.{u} R)} (g : M ⟶ N) :
    (alternatingCofaceMapComplex (Complex R) ⋙
        cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (Functor.whiskerRight g (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0)) ≫
        (coefficientSingleTotalIso N).hom =
      (coefficientSingleTotalIso M).hom ≫
        extendMap ((alternatingCofaceMapComplex (ModuleCat.{u} R)).map g)
          ComplexShape.embeddingUpNat := by
  let S := HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0
  let A := alternatingCofaceMapComplex (ModuleCat.{u} R)
  let T := cochainProductTotalizationFunctor (ModuleCat.{u} R)
  let D := ProductTotal.functor (ModuleCat.{u} R)
  let e := ComplexShape.embeddingUpNat
  let α := alternatingCofaceFunctorIso S
  let β (K : CochainComplex (ModuleCat.{u} R) ℕ) := SerrePositivity.mapExtendIso S K e
  let δ (K : CochainComplex (ModuleCat.{u} R) ℕ) := ProductTotal.singleRowIso (K.extend e)
  have h₁ := congrArg T.map (α.inv.naturality g)
  simp only [Functor.map_comp] at h₁
  change T.map ((alternatingCofaceMapComplex (Complex R)).map (Functor.whiskerRight g S)) ≫
      T.map (α.app N).inv = T.map (α.app M).inv ≫
        T.map ((S.mapHomologicalComplex (.up ℕ)).map (A.map g)) at h₁
  have h₂₀ := SerrePositivity.mapExtendIso_naturality S e (A.map g)
  change (S.mapHomologicalComplex (.up ℤ)).map (extendMap (A.map g) e) ≫
      (β (A.obj N)).hom = (β (A.obj M)).hom ≫
        extendMap ((S.mapHomologicalComplex (.up ℕ)).map (A.map g)) e at h₂₀
  have h₂₁ : extendMap ((S.mapHomologicalComplex (.up ℕ)).map (A.map g)) e ≫
      (β (A.obj N)).inv = (β (A.obj M)).inv ≫
        (S.mapHomologicalComplex (.up ℤ)).map (extendMap (A.map g) e) := by
    apply (cancel_mono (β (A.obj N)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₂₀]
    simp only [Iso.inv_hom_id_assoc]
  have h₂ := congrArg D.map h₂₁
  simp only [Functor.map_comp] at h₂
  have h₃ := (ProductTotal.singleRowNatIso (ModuleCat.{u} R)).hom.naturality
    (extendMap (A.map g) e)
  change D.map ((S.mapHomologicalComplex (.up ℤ)).map (extendMap (A.map g) e)) ≫
      (δ (A.obj N)).hom = (δ (A.obj M)).hom ≫ extendMap (A.map g) e at h₃
  change T.map ((alternatingCofaceMapComplex (Complex R)).map
      (Functor.whiskerRight g S)) ≫ T.map (α.app N).inv ≫ D.map (β (A.obj N)).inv ≫
      (δ (A.obj N)).hom =
    (T.map (α.app M).inv ≫ D.map (β (A.obj M)).inv ≫ (δ (A.obj M)).hom) ≫
      extendMap (A.map g) e
  rw [← Category.assoc, h₁, Category.assoc]
  change T.map (α.app M).inv ≫
    (D.map (extendMap ((S.mapHomologicalComplex (.up ℕ)).map (A.map g)) e) ≫
      D.map (β (A.obj N)).inv) ≫ (δ (A.obj N)).hom = _
  rw [h₂, Category.assoc, Category.assoc, h₃]
  simp only [Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
