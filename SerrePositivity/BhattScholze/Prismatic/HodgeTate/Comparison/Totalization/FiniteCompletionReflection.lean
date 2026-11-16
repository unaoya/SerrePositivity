module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletion
public import Mathlib.CategoryTheory.HomCongr

/-!
# 反復完備化の標準単位の普遍性

## 概要
既存の主元の反映の普遍性を反復し、全座標に完備な標的への射を標準単位で一意に延長する。

## 方針
本体の導来圏の比較同型と Hom 同値を使う。射の同値の前向き射は元の単位との前合成である。

## 規約
反復完備化の単位を別の同型で変更しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限生成イデアルについての標準完備化の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 実際の複体の標準完備化の単位に沿う、完備な標的への射の同値。 -/
def completionHomEquiv (a : R) (K : Complex R) (Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) :
    (complexCompletionObject R a K ⟶ Y) ≃ (DerivedCategory.Q.obj K ⟶ Y) :=
  (Iso.homCongr ((derivedComplexCompletionComparison R a).app K).symm (Iso.refl Y)).trans
    (derivedComplexCompletionHomEquiv R a (DerivedCategory.Q.obj K) Y hY)

/-- この Hom 同値は、具体的な元の標準単位との前合成そのものである。 -/
@[simp] theorem completionHomEquiv_apply (a : R) (K : Complex R) (Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) (f : complexCompletionObject R a K ⟶ Y) :
    completionHomEquiv a K Y hY f = DerivedCategory.Q.map (complexCompletionUnit R a K) ≫ f := by
  change (derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
    ((derivedComplexCompletionComparison R a).hom.app K ≫ f ≫ 𝟙 Y) = _
  rw [Category.comp_id, ← Category.assoc, derivedComplexCompletionUnit_comparison]
  rfl

/-- 全座標に完備な標的への射は、反復した標準単位に沿って一意に延長する。 -/
def finiteCompletionHomEquiv : ∀ {r : ℕ} (x : Fin r → R) (K : Complex R)
    (Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y),
    (DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) ⟶ Y) ≃
      (DerivedCategory.Q.obj K ⟶ Y)
  | 0, _, _, _, _ => Equiv.refl _
  | r+1, x, K, Y, hY =>
    (completionHomEquiv (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K)
      Y (hY (Fin.last r))).trans
        (finiteCompletionHomEquiv (Fin.init x) K Y (fun j => hY j.castSucc))

/-- 反復した射の同値の前向き射も、元の合成単位との前合成である。 -/
@[simp] theorem finiteCompletionHomEquiv_apply {r : ℕ} (x : Fin r → R) (K : Complex R)
    (Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y)
    (f : DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) ⟶ Y) :
    finiteCompletionHomEquiv x K Y hY f = DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ f := by
  induction r with
  | zero =>
    dsimp only [finiteCompletionHomEquiv, finiteCompletionFunctor, finiteCompletionUnit,
      Equiv.refl_apply]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  | succ r ih =>
    change finiteCompletionHomEquiv (Fin.init x) K Y (fun j => hY j.castSucc)
      (completionHomEquiv (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K) Y
        (hY (Fin.last r)) f) =
      DerivedCategory.Q.map (finiteCompletionUnit (Fin.init x) K ≫
        complexCompletionUnit R (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K)) ≫ f
    rw [ih (Fin.init x), completionHomEquiv_apply, Functor.map_comp]
    simp only [Category.assoc]

/-- 全座標に完備な標的への射は、元の合成単位との合成で判定できる。 -/
theorem finiteCompletionHom_ext {r : ℕ} (x : Fin r → R) (K : Complex R)
    (Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y)
    {f g : DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K) ⟶ Y}
    (h : DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ f =
      DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ g) : f = g := by
  apply (finiteCompletionHomEquiv x K Y hY).injective
  simpa only [finiteCompletionHomEquiv_apply] using h

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
