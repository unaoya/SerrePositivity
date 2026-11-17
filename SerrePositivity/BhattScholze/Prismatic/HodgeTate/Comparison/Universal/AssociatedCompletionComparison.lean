module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompleteness

/-!
# 同伴な座標の反復完備化の標準単位を保つ比較

## 概要
各座標を単位倍で変えても、元の反復完備化は標準単位を保つ指定同型で一致する。

## 方針
同じ完備対象への Hom の普遍性で両方向の射を作り、単位に沿う一意性で両逆と自然性を証明する。

## 規約
導来圏上の自然な比較であり、対象ごとに任意の同型を選ばない。

## 使われ方
Construction 6.1 の (α(p),α(d)) と (p,p) の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r : ℕ}
variable (x y : Fin r → R) (h : ∀ j, Associated (x j) (y j))

include h
/-- 同伴な座標への完備化は元の各座標についても完備。 -/
theorem associatedCoordinates_complete (K : Complex R) (j : Fin r) :
    IsComplete R (x j) (DerivedCategory.Q.obj ((finiteCompletionFunctor y).obj K)) :=
  (isComplete_associated_iff (x j) (y j) (h j) _).mpr (finiteCompletion_isComplete y K j)

/-- 各座標を同伴な元に変えた反復完備化の、標準単位を保つ指定同型。 -/
def associatedFiniteCompletionIso (K : Complex R) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) ≅
      DerivedCategory.Q.obj ((finiteCompletionFunctor y).obj K) := by
  let f := (finiteCompletionHomEquiv x K _ (associatedCoordinates_complete x y h K)).symm
    (DerivedCategory.Q.map (finiteCompletionUnit y K))
  let g := (finiteCompletionHomEquiv y K _
    (associatedCoordinates_complete y x (fun j => (h j).symm) K)).symm
      (DerivedCategory.Q.map (finiteCompletionUnit x K))
  have hf : DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ f =
      DerivedCategory.Q.map (finiteCompletionUnit y K) := by
    simpa only [finiteCompletionHomEquiv_apply] using
      (finiteCompletionHomEquiv x K _ (associatedCoordinates_complete x y h K)).apply_symm_apply
        (DerivedCategory.Q.map (finiteCompletionUnit y K))
  have hg : DerivedCategory.Q.map (finiteCompletionUnit y K) ≫ g =
      DerivedCategory.Q.map (finiteCompletionUnit x K) := by
    simpa only [finiteCompletionHomEquiv_apply] using
      (finiteCompletionHomEquiv y K _
      (associatedCoordinates_complete y x (fun j => (h j).symm) K)).apply_symm_apply
        (DerivedCategory.Q.map (finiteCompletionUnit x K))
  refine ⟨f, g, ?_, ?_⟩
  · apply finiteCompletionHom_ext x K _ (finiteCompletion_isComplete x K)
    rw [← Category.assoc, hf, hg, Category.comp_id]
  · apply finiteCompletionHom_ext y K _ (finiteCompletion_isComplete y K)
    rw [← Category.assoc, hg, hf, Category.comp_id]

/-- 指定比較の前向き射は、元の二つの合成単位を一致させる。 -/
theorem associatedFiniteCompletionIso_unit (K : Complex R) :
    DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ (associatedFiniteCompletionIso x y h K).hom =
      DerivedCategory.Q.map (finiteCompletionUnit y K) := by
  simpa only [associatedFiniteCompletionIso, finiteCompletionHomEquiv_apply] using
    (finiteCompletionHomEquiv x K _ (associatedCoordinates_complete x y h K)).apply_symm_apply
        (DerivedCategory.Q.map (finiteCompletionUnit y K))

/-- 指定された比較は、元の複体の射に自然である。 -/
theorem associatedFiniteCompletionIso_naturality {K L : Complex R} (f : K ⟶ L) :
    DerivedCategory.Q.map ((finiteCompletionFunctor x).map f) ≫
        (associatedFiniteCompletionIso x y h L).hom =
      (associatedFiniteCompletionIso x y h K).hom ≫
        DerivedCategory.Q.map ((finiteCompletionFunctor y).map f) := by
  apply finiteCompletionHom_ext x K _ (associatedCoordinates_complete x y h L)
  rw [← Category.assoc, ← Functor.map_comp, ← finiteCompletionUnit_naturality,
    Functor.map_comp, Category.assoc, associatedFiniteCompletionIso_unit,
    ← Category.assoc, associatedFiniteCompletionIso_unit, ← Functor.map_comp,
    finiteCompletionUnit_naturality, Functor.map_comp]

/-- 同伴な座標の指定比較を、元の完備化複体から導来圏への自然同型として読む。 -/
def associatedFiniteCompletionNatIso :
    finiteCompletionFunctor x ⋙ DerivedCategory.Q ≅ finiteCompletionFunctor y ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (associatedFiniteCompletionIso x y h)
    (fun f => associatedFiniteCompletionIso_naturality x y h f)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
