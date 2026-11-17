module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionReflection
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived

/-!
# 反復した導来完備化の元の単位と一意性

## 概要
本体の導来主元完備化の標準単位と Hom 同値を、同じ有限列に沿って合成する。

## 方針
元の単位の合成への前合成が Hom 同値であることを、列の長さの帰納法で確認する。

## 規約
新しい完備化や新しい反映の存在は仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較の源の模型への非依存。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 本体の主元の標準単位を同じ有限列に沿って合成する。 -/
def finiteDerivedCompletionUnit : ∀ {r : ℕ} (x : Fin r → R),
    𝟭 (ConcreteDerivedCategory R) ⟶ finiteDerivedCompletionFunctor x
  | 0, _ => 𝟙 _
  | r+1, x => {
      app X := (finiteDerivedCompletionUnit (Fin.init x)).app X ≫
        (derivedComplexCompletionUnit R (x (Fin.last r))).app
          ((finiteDerivedCompletionFunctor (Fin.init x)).obj X)
      naturality X Y g := by
        change g ≫ ((finiteDerivedCompletionUnit (Fin.init x)).app Y ≫ _) =
          ((finiteDerivedCompletionUnit (Fin.init x)).app X ≫ _) ≫
            (derivedComplexCompletionFunctor R (x (Fin.last r))).map
              ((finiteDerivedCompletionFunctor (Fin.init x)).map g)
        have h₁ := (finiteDerivedCompletionUnit (Fin.init x)).naturality g
        have h₂ := (derivedComplexCompletionUnit R (x (Fin.last r))).naturality
          ((finiteDerivedCompletionFunctor (Fin.init x)).map g)
        simp only [Functor.id_map] at h₁ h₂
        rw [← Category.assoc, h₁, Category.assoc, h₂]
        exact (Category.assoc _ _ _).symm }

/-- 各座標に完備な任意の導来対象への Hom の同値。 -/
def finiteDerivedCompletionHomEquiv : ∀ {r : ℕ} (x : Fin r → R)
    (X Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y),
    ((finiteDerivedCompletionFunctor x).obj X ⟶ Y) ≃ (X ⟶ Y)
  | 0, _, _, _, _ => Equiv.refl _
  | r+1, x, X, Y, hY =>
    (derivedComplexCompletionHomEquiv R (x (Fin.last r))
      ((finiteDerivedCompletionFunctor (Fin.init x)).obj X) Y (hY (Fin.last r))).trans
        (finiteDerivedCompletionHomEquiv (Fin.init x) X Y (fun j => hY j.castSucc))

/-- 元の合成単位への前合成が、その Hom 同値である。 -/
@[simp] theorem finiteDerivedCompletionHomEquiv_apply {r : ℕ} (x : Fin r → R)
    (X Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y)
    (g : (finiteDerivedCompletionFunctor x).obj X ⟶ Y) :
    finiteDerivedCompletionHomEquiv x X Y hY g = (finiteDerivedCompletionUnit x).app X ≫ g := by
  induction r with
  | zero =>
    change g = 𝟙 X ≫ g
    exact (Category.id_comp g).symm
  | succ r ih =>
    change finiteDerivedCompletionHomEquiv (Fin.init x) X Y (fun j => hY j.castSucc)
        (derivedComplexCompletionHomEquiv R (x (Fin.last r))
          ((finiteDerivedCompletionFunctor (Fin.init x)).obj X) Y (hY (Fin.last r)) g) =
      ((finiteDerivedCompletionUnit (Fin.init x)).app X ≫
        (derivedComplexCompletionUnit R (x (Fin.last r))).app
          ((finiteDerivedCompletionFunctor (Fin.init x)).obj X)) ≫ g
    rw [ih (Fin.init x), derivedComplexCompletionHomEquiv_apply]
    exact (Category.assoc _ _ _).symm

/-- 各座標に完備な標的への射は、元の合成単位との合成で判定できる。 -/
theorem finiteDerivedCompletionHom_ext {r : ℕ} (x : Fin r → R)
    (X Y : ConcreteDerivedCategory R) (hY : ∀ j, IsComplete R (x j) Y)
    {g h : (finiteDerivedCompletionFunctor x).obj X ⟶ Y}
    (eq : (finiteDerivedCompletionUnit x).app X ≫ g = (finiteDerivedCompletionUnit x).app X ≫ h) : g = h := by
  apply (finiteDerivedCompletionHomEquiv x X Y hY).injective
  simpa only [finiteDerivedCompletionHomEquiv_apply] using eq

/-- 末尾を一つ加えた既存の比較同型の、元の合成の表示。 -/
theorem finiteDerivedCompletionComparison_succ_hom {r : ℕ} (x : Fin (r+1) → R) (K : Complex R) :
    (finiteDerivedCompletionComparison x).hom.app K =
      (derivedComplexCompletionFunctor R (x (Fin.last r))).map
        ((finiteDerivedCompletionComparison (Fin.init x)).hom.app K) ≫
      (derivedComplexCompletionComparison R (x (Fin.last r))).hom.app
        ((finiteCompletionFunctor (Fin.init x)).obj K) := by
  simp [finiteDerivedCompletionComparison]
  exact Category.id_comp _

/-- 導来の合成単位は、元の複体の合成単位そのものを計算する。 -/
@[reassoc] theorem finiteDerivedCompletionUnit_comparison {r : ℕ} (x : Fin r → R) (K : Complex R) :
    (finiteDerivedCompletionUnit x).app (DerivedCategory.Q.obj K) ≫
        (finiteDerivedCompletionComparison x).hom.app K =
      DerivedCategory.Q.map (finiteCompletionUnit x K) := by
  induction r with
  | zero => simp [finiteDerivedCompletionUnit, finiteDerivedCompletionComparison, finiteCompletionUnit]
  | succ r ih =>
    rw [finiteDerivedCompletionComparison_succ_hom]
    change ((finiteDerivedCompletionUnit (Fin.init x)).app (DerivedCategory.Q.obj K) ≫
      (derivedComplexCompletionUnit R (x (Fin.last r))).app
        ((finiteDerivedCompletionFunctor (Fin.init x)).obj (DerivedCategory.Q.obj K))) ≫ _ = _
    have hn := (derivedComplexCompletionUnit R (x (Fin.last r))).naturality
      ((finiteDerivedCompletionComparison (Fin.init x)).hom.app K)
    simp only [Functor.id_map, Functor.comp_obj] at hn
    simp only [Category.assoc]
    rw [← reassoc_of% hn, reassoc_of% (ih (Fin.init x)),
      derivedComplexCompletionUnit_comparison R (x (Fin.last r))
        ((finiteCompletionFunctor (Fin.init x)).obj K)]
    dsimp only [complexCompletionUnitObject]
    rw [← Functor.map_comp]
    rfl

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
