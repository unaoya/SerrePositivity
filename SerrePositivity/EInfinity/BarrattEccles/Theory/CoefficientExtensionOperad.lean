module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientExtension
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientOperad
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorAdjunctionMate

/-!
# Barratt–Eccles オペラッドの係数拡大

## 概要
Berger–Fresse §1.1 の arity ごとの係数拡大の同型はオペラッドの構造射を保つ。

## 方針
係数制限の比較式の随伴像を取り、強モノイダル構造の逆写像を使う。

## 規約
任意の環準同型を許す。

## 使われ方
M13 の厳密な底変更関手の代数作用。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory DifferentialGraded
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 係数拡大の既存の強モノイダル構造は対称性を保つ。 -/
@[instance_reducible]
def scalarExtensionLaxBraided : (ScalarExtension.extension f).LaxBraided where
  toLaxMonoidal := inferInstance
  braided K L := (ScalarExtension.tensorIso_braiding f K L).symm

/-- arity の型で書いた係数拡大の比較同型。 -/
abbrev coefficientExtensionArityIso (n : ℕ) :
    (ScalarExtension.extension f).obj ((operad S).arity n) ≅ (operad T).arity n :=
  coefficientExtensionIso f n

set_option maxHeartbeats 1200000 in
-- 同じ arity を二つの係数環の対称列で照合する。
/-- オペラッドの係数拡大の比較同型は入力置換と可換。 -/
lemma coefficientExtension_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LaxComparisonSquare (ScalarExtension.extension f)
      (coefficientExtensionArityIso f n).inv (coefficientExtensionArityIso f n).inv
      ((operad T).sequence.map (FiniteBijection.permutation n σ))
      ((operad S).sequence.map (FiniteBijection.permutation n σ)) := by
  let L := ScalarExtension.extension f
  let R := ScalarExtension.restriction f
  let A := ScalarExtension.adjunction f
  let σ' := FiniteBijection.permutation n σ
  let c : (operad S).arity n ⟶ R.obj ((operad T).arity n) := coefficientComplexMap f n
  let e : L.obj ((operad S).arity n) ≅ (operad T).arity n := coefficientExtensionIso f n
  have h : (operad S).sequence.map σ' ≫ c =
      c ≫ R.map ((operad T).sequence.map σ') := (coefficientSequenceMap f).naturality σ'
  have h' := congrArg (A.homEquiv ((operad S).arity n) ((operad T).arity n)).symm h
  rw [A.homEquiv_naturality_left_symm, A.homEquiv_naturality_right_symm] at h'
  change L.map ((operad S).sequence.map σ') ≫ e.hom = e.hom ≫
    (operad T).sequence.map σ' at h'
  change (operad T).sequence.map σ' ≫ e.inv = e.inv ≫ L.map ((operad S).sequence.map σ')
  apply (cancel_epi e.hom).mp
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact h'.symm

/-- オペラッドの係数拡大の比較同型は単位演算と可換。 -/
lemma coefficientExtension_unit :
    LaxComparisonSquare (ScalarExtension.extension f) (ε (ScalarExtension.extension f))
      (coefficientExtensionIso f 1).inv (operad T).unit (operad S).unit := by
  let A := ScalarExtension.adjunction f
  have h := congrArg (A.homEquiv _ _).symm (coefficientComplexMap_unit f)
  rw [A.homEquiv_naturality_left_symm, A.homEquiv_naturality_right_symm,
    laxUnit_mate A] at h
  unfold LaxComparisonSquare
  apply (cancel_epi (η (ScalarExtension.extension f))).mp
  apply (cancel_mono (coefficientExtensionIso f 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.Monoidal.η_ε_assoc]
  exact h.symm

/-- オペラッドの係数拡大の比較同型は部分合成と可換。 -/
lemma coefficientExtension_partialComposition (m n : ℕ) (i : Fin (m + 1)) :
    LaxComparisonSquare (ScalarExtension.extension f)
      (laxTensorComparison (ScalarExtension.extension f)
        (coefficientExtensionIso f (m + 1)).inv (coefficientExtensionIso f n).inv)
      (coefficientExtensionIso f (m + n)).inv ((operad T).comp m n i) ((operad S).comp m n i) := by
  let L := ScalarExtension.extension f
  let A := ScalarExtension.adjunction f
  let e (k : ℕ) : L.obj ((operad S).arity k) ≅ (operad T).arity k :=
    coefficientExtensionIso f k
  have hs : (operad S).comp m n i ≫ coefficientComplexMap f (m + n) =
      laxTensorComparison (ScalarExtension.restriction f)
        (coefficientComplexMap f (m + 1)) (coefficientComplexMap f n) ≫
          (ScalarExtension.restriction f).map ((operad T).comp m n i) :=
    coefficientComplexMap_partialComposition f m n i
  have h := congrArg (A.homEquiv _ _).symm hs
  rw [A.homEquiv_naturality_left_symm, A.homEquiv_naturality_right_symm,
    laxTensorComparison_mate A] at h
  change L.map ((operad S).comp m n i) ≫ (e (m + n)).hom =
    δ L _ _ ≫ ((e (m + 1)).hom ⊗ₘ (e n).hom) ≫ (operad T).comp m n i at h
  change _ ≫ (e (m + n)).inv =
    laxTensorComparison L (e (m + 1)).inv (e n).inv ≫ L.map ((operad S).comp m n i)
  apply (cancel_mono (e (m + n)).hom).mp
  simp only [laxTensorComparison, Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
    Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc, tensorHom_id,
    id_whiskerRight, Category.id_comp]

end SerrePositivity.EInfinity.BarrattEccles
