module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComparison

/-!
# 標準 S 線形 Tot 比較の指定行成分

## 概要
元の随伴の単位から作った比較の行成分は、元の R 行射影を通常の係数拡大で写した射である。

## 方針
加群随伴で転置し、係数制限の指定同型の逆の行成分を相殺する。

## 規約
元の単位と指定行射影を使い、成分公式を比較の仮定にしない。

## 使われ方
BS 著者版 Lemma 4.22 の固定係数増大と標準 S 線形比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 係数制限の指定 Tot 同型の逆は、元の指定行射影を保つ。 -/
@[reassoc] theorem restrictionTotalIso_inv_π (f : R →+* S)
    (K : CochainComplex (Complex S) ℕ) (q : ℤ) (n : ℕ) :
    (restrictionTotalIso f K).inv.f q ≫ (ModuleCat.restrictScalars f).map (componentπ K n q) =
      componentπ (restrictedRows f K) n q := by
  let e := (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) q).mapIso (restrictionTotalIso f K)
  have hp : e.hom ≫ componentπ (restrictedRows f K) n q =
      (ModuleCat.restrictScalars f).map (componentπ K n q) := restrictionTotalDegree_π f K q n
  change e.inv ≫ (ModuleCat.restrictScalars f).map (componentπ K n q) = _
  rw [← hp, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- 通常の係数拡大の元の標準 Tot 比較の行成分。 -/
@[reassoc] theorem baseChangeTotalComparison_component (f : R →+* S)
    (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n : ℕ) :
    (baseChangeTotalComparison f K).f q ≫
      componentπ ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).obj K) n q = (ModuleCat.extendScalars f).map (componentπ K n q) := by
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [baseChangeTotalComparison, Equiv.apply_symm_apply]
  have hr := (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_left
    (componentπ K n q) (𝟙 _)
  simp only [Category.comp_id, Adjunction.homEquiv_id] at hr
  erw [hr]
  change ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (rowsBaseChangeUnit f K)).f q ≫
      (restrictionTotalIso f _).inv.f q ≫ (ModuleCat.restrictScalars f).map
        (componentπ ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
          (.up ℕ)).obj K) n q) = _
  rw [restrictionTotalIso_inv_π, componentπ_naturality]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
