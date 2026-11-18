module

public import SerrePositivity.EInfinity.BarrattEccles.Basis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Barratt–Eccles の演算複体と始代数の K 平坦性

## 概要
Berger–Fresse §1.1 の正規化鎖の各 arity と、セル構成の始代数を扱う。

## 方針
非退化単体の基底と上有界性を使う。零複体の自由代数は零入力成分で計算する。

## 規約
基礎環の標数を制限せず、非有界な acyclic 複体とのテンソルを扱う。

## 使われ方
HA §3.2.2 の係数拡大で、cofibrant 代数の台の K 平坦性を示す際の始段。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped ZeroObject

variable (A : Type u) [CommRing A]

/-- Berger–Fresse §1.1 の各演算複体は基礎環上で K 平坦。 -/
lemma complexArity_kFlat (n : ℕ) : complexKFlat A (complex A n) := by
  apply complexKFlat_of_flat_boundedAbove A (complex A n) 0
  · exact complex_isZero_positive A n
  · intro i
    by_cases hi : 0 < i
    · have := ModuleCat.subsingleton_of_isZero (complex_isZero_positive A n i hi)
      infer_instance
    · let q := Int.toNat (-i)
      have hq : -(q : ℤ) = i := by
        dsimp [q]
        omega
      rw [← hq]
      have := Module.Free.of_basis (complexBasis A n q)
      exact Module.Flat.of_free

/-- 空の生成元から作った始代数の台は零入力の演算複体と同型。 -/
lemma initialAlgebraCarrier_kFlat (X : (operad A).Algebra) (hX : IsInitial X) :
    complexKFlat A X.carrier := by
  let P := operad A
  let F := P.freeAlgebraFunctor
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P
  have : F.IsLeftAdjoint := P.freeAlgebraAdjunction.isLeftAdjoint
  let h0 : IsInitial (F.obj (0 : Complex A)) := (isZero_zero (Complex A)).isInitial.isInitialObj F _
  let e := U.mapIso (hX.uniqueUpToIso h0)
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence (0 : Complex A) 0
  have : IsIso j := schurι_zero_isIso A P.sequence
  exact complexKFlat_of_iso A (e ≪≫ (asIso j).symm ≪≫ ρ_ (complex A 0))
    (complexArity_kFlat A 0)

end SerrePositivity.EInfinity.BarrattEccles
