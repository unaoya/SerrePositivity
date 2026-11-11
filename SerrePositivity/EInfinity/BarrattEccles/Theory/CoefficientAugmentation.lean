module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientOperad
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationCochainValues
public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorComparison

/-!
# Barratt–Eccles の augmentation と係数制限

## 概要
Berger–Fresse §1.1 の可換オペラッドへの augmentation は、係数変更と可換。

## 方針
零次の生成元は 1 に送られ、他の次数では余域が零になることを使う。

## 規約
任意の環準同型とすべての arity。

## 使われ方
M13 の離散代数と係数制限の比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- arity ごとの augmentation と係数写像は、係数制限の単位比較と可換。 -/
lemma coefficientComplexMap_augmentation (n : ℕ) :
    LaxComparisonSquare (ScalarExtension.restriction f) (coefficientComplexMap f n)
      (Functor.LaxMonoidal.ε (ScalarExtension.restriction f))
      ((augmentation S).map.app (FiniteBijection.of n))
      ((augmentation T).map.app (FiniteBijection.of n)) := by
  let R := ScalarExtension.restriction f
  change complexAugmentation S n ≫ Functor.LaxMonoidal.ε R =
    coefficientComplexMap f n ≫ R.map (complexAugmentation T n)
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    apply (cancel_epi (complexXIso S n 0).inv).mp
    apply normalizedGenerator_hom_ext S
    intro x
    let s := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))
    let t := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat T))
    let a := (complexXIso S n 0).inv (normalizedGenerator S n 0 x)
    let b := (complexXIso T n 0).inv (normalizedGenerator T n 0 x)
    have ha : (complexAugmentation S n).f 0 a = s.inv (1 : S) := by
      apply s.toLinearEquiv.injective
      change s.hom ((complexAugmentation S n).f 0 a) = s.hom (s.inv 1)
      rw [Iso.inv_hom_id_apply]
      exact complexAugmentation_generator_zero S n x
    have hb : (complexAugmentation T n).f 0 b = t.inv (1 : T) := by
      apply t.toLinearEquiv.injective
      change t.hom ((complexAugmentation T n).f 0 b) = t.hom (t.inv 1)
      rw [Iso.inv_hom_id_apply]
      exact complexAugmentation_generator_zero T n x
    change (Functor.LaxMonoidal.ε R).f 0 ((complexAugmentation S n).f 0 a) =
      (complexAugmentation T n).f 0 ((coefficientComplexMap f n).f 0 a)
    rw [ha, ScalarExtension.restriction_ε_one]
    have hc : (coefficientComplexMap f n).f 0 a = b :=
      coefficientComplexMap_generator f n 0 x
    exact (congrArg (fun z => (complexAugmentation T n).f 0 z) hc |>.trans hb).symm
  · exact ((ModuleCat.restrictScalars f).map_isZero
      (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat T)) i hi)).eq_of_tgt _ _

end SerrePositivity.EInfinity.BarrattEccles
