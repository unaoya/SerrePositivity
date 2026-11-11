module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientChains
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.EInfinity.BarrattEccles.TensorComplexGenerators

/-!
# Barratt–Eccles オペラッドの係数写像

## 概要
Berger–Fresse §1.1 の演算の係数写像が、置換・単位・部分合成と可換であることを示す。

## 方針
正規化生成元と、既存の係数制限のテンソル比較を評価する。

## 規約
零入力の演算を含め、基礎環の射に平坦性を要求しない。

## 使われ方
Barratt–Eccles 代数の係数変更。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open scoped Simplicial TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 係数写像は単体集合の射が誘導する鎖写像と可換。 -/
lemma coefficientComplexMap_naturality {m n : ℕ} (g : simplicial m ⟶ simplicial n) :
    (normalizedFunctor S).map g ≫ coefficientComplexMap f n =
      coefficientComplexMap f m ≫ (ScalarExtension.restriction f).map
        ((normalizedFunctor T).map g) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (complex_isZero_positive S m i hi).eq_of_src _ _
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(q : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (complexXIso S m q).inv).mp
  apply normalizedGenerator_hom_ext S
  intro x
  change (coefficientComplexMap f n).f (-(q : ℤ))
      (((normalizedFunctor S).map g).f (-(q : ℤ))
        ((complexXIso S m q).inv (normalizedGenerator S m q x))) =
    ((normalizedFunctor T).map g).f (-(q : ℤ))
      ((coefficientComplexMap f m).f (-(q : ℤ))
        ((complexXIso S m q).inv (normalizedGenerator S m q x)))
  rw [complexXIso_inv_naturality_apply S, normalizedChainMap_generator,
    coefficientComplexMap_generator, coefficientComplexMap_generator,
    complexXIso_inv_naturality_apply T, normalizedChainMap_generator]

/-- オペラッドの対称列の係数写像。 -/
def coefficientSequenceMap : sequence S ⟶ sequence T ⋙ ScalarExtension.restriction f where
  app X := coefficientComplexMap f X.card
  naturality {_ _} g := coefficientComplexMap_naturality f (simplicialSequenceMap g)

/-- オペラッドの単位は、係数制限の lax monoidal 単位と可換。 -/
lemma coefficientComplexMap_unit :
    unit S ≫ coefficientComplexMap f 1 =
      Functor.LaxMonoidal.ε (ScalarExtension.restriction f) ≫
        (ScalarExtension.restriction f).map (unit T) := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (coefficientComplexMap f 1).f 0
      ((unit S).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv (1 : S))) =
    (unit T).f 0 ((Functor.LaxMonoidal.ε (ScalarExtension.restriction f)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv (1 : S)))
  rw [ScalarExtension.restriction_ε_one, unit_zero_apply, unit_zero_apply, one_smul, one_smul]
  exact coefficientComplexMap_generator f 1 0 unitSimplex

/-- 係数写像は正規化された shuffle の符号付き和を保つ。 -/
lemma normalizedCoefficientComponent_shuffleValue (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    normalizedCoefficientComponent f (m + n) (p + q) (shuffleValue S m n i p q x y) =
      shuffleValue T m n i p q x y := by
  simp only [shuffleValue, map_sum, map_zsmul, normalizedCoefficientComponent_generator]

set_option maxHeartbeats 800000 in
-- 二つの係数環のテンソル成分を同時に照合する。
/-- オペラッドの部分合成は、係数制限の lax monoidal テンソルと可換。 -/
lemma coefficientComplexMap_partialComposition (m n : ℕ) (i : Fin (m + 1)) :
    partialComposition S m n i ≫ coefficientComplexMap f (m + n) =
      (coefficientComplexMap f (m + 1) ⊗ₘ coefficientComplexMap f n) ≫
        Functor.LaxMonoidal.μ (ScalarExtension.restriction f)
          (complex T (m + 1)) (complex T n) ≫
        (ScalarExtension.restriction f).map (partialComposition T m n i) := by
  apply tensor_complex_generator_hom_ext S (m + 1) n
  intro p q x y
  let X := complex S (m + 1)
  let Y := complex S n
  let X' := complex T (m + 1)
  let Y' := complex T n
  let F := ScalarExtension.restriction f
  let r := -(p : ℤ)
  let s := -(q : ℤ)
  let t := -((p + q : ℕ) : ℤ)
  have h : r + s = t := by dsimp [r, s, t]; omega
  let a : X.X r := (complexXIso S (m + 1) p).inv (normalizedGenerator S (m + 1) p x)
  let b : Y.X s := (complexXIso S n q).inv (normalizedGenerator S n q y)
  let a' : X'.X r := (complexXIso T (m + 1) p).inv (normalizedGenerator T (m + 1) p x)
  let b' : Y'.X s := (complexXIso T n q).inv (normalizedGenerator T n q y)
  let ar : (F.obj X').X r := a'
  let br : (F.obj Y').X s := b'
  let v := ιTensorObj X Y r s t h (a ⊗ₜ[S] b)
  change (coefficientComplexMap f (m + n)).f t ((partialComposition S m n i).f t v) =
    (partialComposition T m n i).f t
      ((Functor.LaxMonoidal.μ F X' Y').f t
        (((coefficientComplexMap f (m + 1)) ⊗ₘ (coefficientComplexMap f n)).f t v))
  have hv : (((coefficientComplexMap f (m + 1)) ⊗ₘ (coefficientComplexMap f n)).f t v) =
      ιTensorObj (F.obj X') (F.obj Y') r s t h (ar ⊗ₜ[S] br) := by
    exact (tensorMap_apply (coefficientComplexMap f (m + 1)) (coefficientComplexMap f n)
      r s t h a b).trans (congrArg (fun w => ιTensorObj (F.obj X') (F.obj Y') r s t h w)
      (congrArg₂ (fun (v : (F.obj X').X r) (w : (F.obj Y').X s) => v ⊗ₜ[S] w)
        (coefficientComplexMap_generator f (m + 1) p x)
        (coefficientComplexMap_generator f n q y)))
  rw [hv, ScalarExtension.restriction_μ_apply f X' Y' r s t h a' b']
  have hS := partialComposition_neg_tmul S m n i p q a b
  have hT := partialComposition_neg_tmul T m n i p q a' b'
  change (partialComposition S m n i).f t v = _ at hS
  change (partialComposition T m n i).f t (ιTensorObj X' Y' r s t h (a' ⊗ₜ[T] b')) = _ at hT
  rw [hS, hT]
  dsimp only [a, b, a', b']
  simp only [Iso.inv_hom_id_apply, shuffleBilinear_generators]
  have hv' := coefficientComplexMap_f_neg f (m + n) (p + q)
  change (coefficientComplexMap f (m + n)).f t = _ at hv'
  rw [hv']
  simp only [ModuleCat.comp_apply]
  have he := congrArg (fun g => g (shuffleValue S m n i p q x y))
    (complexXIso S (m + n) (p + q)).inv_hom_id
  change (complexXIso S (m + n) (p + q)).hom
    ((complexXIso S (m + n) (p + q)).inv (shuffleValue S m n i p q x y)) = _ at he
  rw [he]
  change (complexXIso T (m + n) (p + q)).inv
    (normalizedCoefficientComponent f (m + n) (p + q) (shuffleValue S m n i p q x y)) = _
  rw [normalizedCoefficientComponent_shuffleValue]

end SerrePositivity.EInfinity.BarrattEccles
