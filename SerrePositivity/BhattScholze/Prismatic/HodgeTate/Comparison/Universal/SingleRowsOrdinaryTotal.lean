module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComponents

/-!
# 零次に集中した元の行の通常係数拡大と積Tot

## 概要
縦次数零に集中した行について、元の標準通常底変換–Tot比較自体が同型になる。

## 方針
指定射影以外の成分の零性を使い、元の各全次数の唯一の非零射影を同型にする。

## 規約
係数拡大の平坦性は要求しない。比較は元の随伴単位から定義したもの。

## 使われ方
元の標準完備比較を通常係数拡大の増大と照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open DifferentialGraded HomologicalAlgebra HomologicalAlgebra.CochainProductTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 他の成分が零の全次数では、同じ指定成分の射影が同型。 -/
def isolatedTotalComponentIso (K : CochainComplex (Complex R) ℕ) (q : ℤ) (n : ℕ)
    (h : ∀ m : ℕ, m ≠ n → IsZero ((K.X m).X (q-m))) :
    (total K).X q ≅ (K.X n).X (q-n) where
  hom := componentπ K n q
  inv := componentLift K q (fun m => if hm : m = n then
    eqToHom (by subst m; rfl) else 0)
  hom_inv_id := by
    apply component_hom_ext K q
    intro m
    by_cases hm : m = n
    · subst m
      simp only [Category.assoc, componentLift_π, dite_true, eqToHom_refl,
        Category.comp_id, Category.id_comp]
    · exact (h m hm).eq_of_tgt _ _
  inv_hom_id := by simp only [componentLift_π, dite_true, eqToHom_refl]

/-- 全成分が零なら、元の同じ全次数の加群は零。 -/
theorem totalDegree_isZero_of_components (K : CochainComplex (Complex R) ℕ) (q : ℤ)
    (h : ∀ m : ℕ, IsZero ((K.X m).X (q-m))) : IsZero ((total K).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply component_hom_ext K q
  intro m
  exact (h m).eq_of_tgt _ _

/-- 元の縦零次集中した行について、元の標準通常係数拡大–Tot比較は同型。 -/
theorem baseChangeTotalComparison_isIso_of_singleRows (f : R →+* S)
    (K : CochainComplex (Complex R) ℕ)
    (h : ∀ n : ℕ, ∀ j : ℤ, j ≠ 0 → IsZero ((K.X n).X j)) :
    IsIso (baseChangeTotalComparison f K) := by
  let E := ModuleCat.extendScalars f
  let L := (baseChangeRowsFunctor f).obj K
  have hL (n : ℕ) (j : ℤ) (hj : j ≠ 0) : IsZero ((L.X n).X j) := E.map_isZero (h n j hj)
  haveI (q : ℤ) : IsIso ((baseChangeTotalComparison f K).f q) := by
    by_cases hq : 0 ≤ q
    · lift q to ℕ using hq
      have hs (m : ℕ) (hm : m ≠ q) : IsZero ((K.X m).X ((q : ℤ)-m)) :=
        h m _ (by omega)
      have ht (m : ℕ) (hm : m ≠ q) : IsZero ((L.X m).X ((q : ℤ)-m)) :=
        hL m _ (by omega)
      haveI : IsIso (componentπ K q (q : ℤ)) :=
        (isolatedTotalComponentIso K q q hs).isIso_hom
      haveI : IsIso (componentπ L q (q : ℤ)) :=
        (isolatedTotalComponentIso L q q ht).isIso_hom
      haveI : IsIso ((baseChangeTotalComparison f K).f q ≫ componentπ L q q) := by
        rw [baseChangeTotalComparison_component]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (componentπ L q q)
    · have hs := totalDegree_isZero_of_components K q (fun m => h m _ (by omega))
      have ht := totalDegree_isZero_of_components L q (fun m => hL m _ (by omega))
      have hz := E.map_isZero hs
      have he : (baseChangeTotalComparison f K).f q = (hz.iso ht).hom := hz.eq_of_src _ _
      rw [he]
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
