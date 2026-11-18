module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientAugmentation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebraFunctor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraRestriction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso

/-!
# 可換モノイド複体の代数作用と係数制限

## 概要
Berger–Fresse §1.1 の augmentation で得る作用を、任意の係数制限と比べる。

## 方針
単位・二項積を保つ複体の比較を、テンソル冪と反復積へ延ばす。

## 規約
可換モノイド複体は零次に集中する必要がない。

## 使われ方
M13 の離散代数、厳密な可換 dg 代数の係数制限。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers

section LaxMonoidal

open Functor.LaxMonoidal (ε left_unitality)
open scoped MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]

/-- 単位を含むテンソル比較は左単位子と可換。 -/
lemma laxComparison_leftUnitor {U : C} {U' : D} (u : U' ⟶ F.obj U) :
    LaxComparisonSquare F (laxTensorComparison F (ε F) u) u (λ_ U').hom (λ_ U).hom := by
  unfold LaxComparisonSquare
  simp only [laxTensorComparison, tensorHom_def', Category.assoc]
  rw [← left_unitality, leftUnitor_naturality]

/-- 単位と積について可換な比較は、すべての反復積についても可換。 -/
lemma laxComparison_powerProduct {X : C} [MonObj X] {Y : D} [MonObj Y]
    (c : Y ⟶ F.obj X)
    (hOne : LaxComparisonSquare F (ε F) c η[Y] η[X])
    (hMul : LaxComparisonSquare F (laxTensorComparison F c c) c μ[Y] μ[X]) (n : ℕ) :
    LaxComparisonSquare F (TensorPowers.map c n ≫ laxPowerComparison F X n) c
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct Y n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n) := by
  induction n with
  | zero =>
    change LaxComparisonSquare F (𝟙 (𝟙_ D) ≫ ε F) c η[Y] η[X]
    rw [Category.id_comp]
    exact hOne
  | succ n ih =>
    have h := LaxComparisonSquare.comp F (LaxComparisonSquare.whiskerLeft F c ih) hMul
    have hc :
        TensorPowers.map c (n + 1) ≫ laxPowerComparison F X (n + 1) =
          laxTensorComparison F c (TensorPowers.map c n ≫ laxPowerComparison F X n) := by
      simp only [laxTensorComparison, TensorPowers.map, laxPowerComparison]
      rw [tensorHom_comp_whiskerLeft_assoc]
    rw [hc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct]
    exact h

end LaxMonoidal

namespace BarrattEccles

open Functor.LaxMonoidal (ε left_unitality)
open scoped MonObj

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 可換モノイド複体から得る厳密な Barratt–Eccles 代数。 -/
def cdgaAlgebraFunctor (A : Type u) [CommRing A] :
    CommMon (Complex A) ⥤ (operad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebra (augmentation A)

/-- 底の比較が単位と積を保てば、augmentation による全 arity の作用を保つ。 -/
def cdgaCoefficientRestrictionIso (X : CommMon (Complex T)) (Y : CommMon (Complex S))
    (e : Y.X ≅ (ScalarExtension.restriction f).obj X.X)
    (hOne : LaxComparisonSquare (ScalarExtension.restriction f)
      (ε (ScalarExtension.restriction f)) e.hom η[Y.X] η[X.X])
    (hMul : LaxComparisonSquare (ScalarExtension.restriction f)
      (laxTensorComparison (ScalarExtension.restriction f) e.hom e.hom) e.hom
      μ[Y.X] μ[X.X]) :
    (cdgaAlgebraFunctor S).obj Y ≅
      (coefficientRestriction f).obj ((cdgaAlgebraFunctor T).obj X) := by
  let R := ScalarExtension.restriction f
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso e (fun n => ?_)
  let c : (operad S).arity n ⟶ R.obj ((operad T).arity n) := coefficientComplexMap f n
  let p := laxPowerComparison R X.X n
  let q := TensorPowers.map e.hom n ≫ p
  have h₁ := LaxComparisonSquare.whiskerRight R q (coefficientComplexMap_augmentation f n)
  have h₂ := laxComparison_leftUnitor R q
  have h₃ := laxComparison_powerProduct R e.hom hOne hMul n
  have h := LaxComparisonSquare.comp R h₁ (LaxComparisonSquare.comp R h₂ h₃)
  unfold LaxComparisonSquare at h
  let a (A : Type u) [CommRing A] (U : CommMon (Complex A)) :=
    ((augmentation A).map.app (FiniteBijection.of n) ▷ power U.X n) ≫
      (λ_ (power U.X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct U.X n
  change a S Y ≫ e.hom = (𝟙 ((operad S).arity n) ⊗ₘ TensorPowers.map e.hom n) ≫
    laxTensorComparison R c p ≫ R.map (a T X)
  have hc : (𝟙 ((operad S).arity n) ⊗ₘ TensorPowers.map e.hom n) ≫
      laxTensorComparison R c p = laxTensorComparison R c q := by
    simp only [laxTensorComparison, tensorHom_comp_tensorHom_assoc, Category.id_comp, q]
  rw [reassoc_of% hc]
  simpa only [a, Category.assoc] using h

end BarrattEccles

end SerrePositivity.EInfinity
