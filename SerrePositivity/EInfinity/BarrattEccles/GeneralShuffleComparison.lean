module

public import SerrePositivity.EInfinity.BarrattEccles.SimplicialPartialComposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleChainMap
public import SerrePositivity.EInfinity.Shuffle.CochainMap
public import SerrePositivity.EInfinity.NegativeTensor.BinaryEvaluation

/-!
# 一般 shuffle と既存 BE 部分合成の比較

概要：Berger–Fresse §1.1.3 の既存の BE 部分合成を一般 shuffle と単体的部分合成へ分解する。
方針：負次数テンソル比較を前置し、正規化生成元上で同じ shuffle 和へ帰着する。
規約：既存の BE 部分合成そのものの等式を証明し、定義を置き換えない。
使われ方：一般 shuffle の AW 余積適合性を BE 部分合成へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：一般 shuffle 和の単体的部分合成による像は既存の BE shuffle 和（BF §1.1.3）。
方針：正規化鎖写像を和へ分配し各積単体の像を同定する。
規約：退化した入力も含む。
使われ方：既存の BE 部分合成の生成元公式との比較。 -/
lemma generalShuffle_value (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (AlexanderWhitney.chainMap A (simplicialPartialComposition m n i)).f (p + q)
        (Shuffle.value A (simplicial (m + 1)) (simplicial n) p q x y) =
      shuffleValue A m n i p q x y := by
  simp only [Shuffle.value, map_sum, map_zsmul, AlexanderWhitney.chainMap_generator,
    simplicialPartialComposition_shuffle, shuffleValue]
  rfl

/-- 概要：既存 BE 部分合成は一般 shuffle と単体的合成の像の合成（BF §1.1.3）。
方針：比較同型で自然数鎖へ戻し、生成元上で shuffle 和を比較する。
規約：整数コチェイン複体の射の等式として述べる。
使われ方：Hopf 対角と既存 BE 部分合成の可換性。 -/
lemma partialComposition_eq_generalShuffle (m n : ℕ) (i : Fin (m + 1)) :
    partialComposition A m n i =
      Shuffle.cochainMap A (simplicial (m + 1)) (simplicial n) ≫
        AlexanderWhitney.cochainMap A (simplicialPartialComposition m n i) := by
  apply (cancel_epi (NegativeTensor.comparison (normalizedChains A (m + 1))
    (normalizedChains A n)).hom).1
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : 0 < j
  · exact (NegativeTensor.isZero_positive (NatTensor.tensor (normalizedChains A (m + 1))
      (normalizedChains A n)) j hj).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = -(k : ℤ) := ⟨(-j).toNat, by omega⟩
  apply (cancel_epi (NegativeTensor.xIso (NatTensor.tensor (normalizedChains A (m + 1))
    (normalizedChains A n)) k).inv).1
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  subst k
  apply Shuffle.tensor_generator_hom_ext A (simplicial (m + 1)) (simplicial n) p q
  intro x y
  let v := ιTensorObj (normalizedChains A (m + 1)) (normalizedChains A n) p q (p + q) rfl
    (AlexanderWhitney.generator A (simplicial (m + 1)) p x ⊗ₜ[A]
      AlexanderWhitney.generator A (simplicial n) q y)
  change (partialComposition A m n i).f (-((p + q : ℕ) : ℤ))
      ((NegativeTensor.comparison (normalizedChains A (m + 1)) (normalizedChains A n)).hom.f
        (-((p + q : ℕ) : ℤ))
        ((NegativeTensor.xIso (NatTensor.tensor (normalizedChains A (m + 1))
          (normalizedChains A n)) (p + q)).inv v)) =
    (AlexanderWhitney.cochainMap A (simplicialPartialComposition m n i)).f (-((p + q : ℕ) : ℤ))
      ((Shuffle.cochainMap A (simplicial (m + 1)) (simplicial n)).f (-((p + q : ℕ) : ℤ))
        ((NegativeTensor.comparison (normalizedChains A (m + 1)) (normalizedChains A n)).hom.f
          (-((p + q : ℕ) : ℤ))
          ((NegativeTensor.xIso (NatTensor.tensor (normalizedChains A (m + 1))
            (normalizedChains A n)) (p + q)).inv v)))
  simp only [v, NegativeTensor.comparison_neg_inv_apply, NegativeTensor.degreeMap_ι_tmul,
    Shuffle.cochainMap]
  erw [partialComposition_neg_tmul A m n i p q]
  erw [NegativeTensor.binaryMap_neg_tmul
    (Shuffle.chainMap A (simplicial (m + 1)) (simplicial n)) p q (p + q) rfl]
  have hs := congrArg (fun g => g (AlexanderWhitney.generator A (simplicial (m + 1)) p x ⊗ₜ[A]
    AlexanderWhitney.generator A (simplicial n) q y))
      (Shuffle.ι_chainMap A (simplicial (m + 1)) (simplicial n) p q)
  rw [show (Shuffle.chainMap A (simplicial (m + 1)) (simplicial n)).f (p + q) v =
      Shuffle.value A (simplicial (m + 1)) (simplicial n) p q x y from
    hs.trans (Shuffle.component_generators A _ _ p q x y)]
  change _ = (extendMap (AlexanderWhitney.chainMap A (simplicialPartialComposition m n i))
    ComplexShape.embeddingDownNat).f (-((p + q : ℕ) : ℤ)) _
  rw [NegativeTensor.extendMap_neg_inv_apply, generalShuffle_value]
  change (complexXIso A (m + n) (p + q)).inv
      (shuffleBilinear A m n i p q
        ((complexXIso A (m + 1) p).hom
          ((complexXIso A (m + 1) p).inv (normalizedGenerator A (m + 1) p x)))
        ((complexXIso A n q).hom ((complexXIso A n q).inv (normalizedGenerator A n q y)))) =
    (complexXIso A (m + n) (p + q)).inv (shuffleValue A m n i p q x y)
  simp only [Iso.inv_hom_id_apply, shuffleBilinear_generators]

end SerrePositivity.EInfinity.BarrattEccles
