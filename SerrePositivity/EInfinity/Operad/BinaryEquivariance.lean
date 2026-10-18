module

public import SerrePositivity.EInfinity.Operad.BinaryInterchange
public import SerrePositivity.EInfinity.Operad.BinaryOutputSwap
public import SerrePositivity.EInfinity.Operad.ArityBijectionTransport
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionSwap

/-!
# 二入力の合成の外側等変性

概要：Berger–Moerdijk §1 の二入力の合成で、外側の入力交換が内側の係数と出力のブロック交換と両立することを証明する。
方針：部分合成の外側等変性を二回適用し、部分合成の交換則で順序をそろえる。
規約：内側の係数の交換は Koszul 対称性、出力は標準有限集合のブロック全単射を使う。
使われ方：全入力への合成の外側等変性を隣接交換から証明する基底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：二入力の合成は外側の入力交換と内側係数の Koszul 交換に関して等変である（Berger–Moerdijk §1）。
方針：最初の代入と次の代入の外側等変性を順に適用し、出力の置換をブロック交換へ移す。
規約：終域の arity は交換後の b+a とする。
使われ方：自由代数の二入力の外側等変性と全入力への帰納法に用いる。 -/
lemma binaryComposition_outer_equivariance (P : Operad A) (a b : ℕ) :
    (P.sequence.map (FiniteBijection.permutation 2 operadTwoSwap) ⊗ₘ
      (β_ (P.arity a) (P.arity b)).hom) ≫ P.binaryComposition b a =
        P.binaryComposition a b ≫ P.sequence.map
          (FiniteBijection.homOfEquiv (X := FiniteBijection.of (a + b))
            (Y := FiniteBijection.of (b + a)) (operadBlockSwap a b)) := by
  let C := P.arity 2
  let U := P.arity a
  let V := P.arity b
  let A₀ := P.sequence.map (FiniteBijection.permutation 2 operadTwoSwap)
  let t := P.sequence.map (FiniteBijection.permutation (1 + a)
    (operadOuterPermutation 1 a 0 operadTwoSwap))
  let t' := P.sequence.map (FiniteBijection.permutation ((0 + a) + 1) (operadTwoSwapAfterFirst a))
  let w := P.sequence.map (FiniteBijection.permutation ((0 + a) + b) (operadTwoSwapOutput a b))
  let c := eqToHom (congrArg P.arity (by omega : 1 + a = (0 + a) + 1))
  let u := eqToHom (congrArg P.arity (by omega : (0 + a) + b = a + b))
  let v := eqToHom (congrArg P.arity (by omega : (0 + a) + b = b + a))
  let f₀ := P.comp 1 a 0
  let f₁ := P.comp 1 a 1
  let g₀ := P.comp (0 + a) b 0
  let g₁ := P.comp (0 + a) b ⟨a, by omega⟩
  let B := P.sequence.map (FiniteBijection.homOfEquiv (X := FiniteBijection.of (a + b))
    (Y := FiniteBijection.of (b + a)) (operadBlockSwap a b))
  have hfirst : (A₀ ▷ U) ≫ f₁ = f₀ ≫ t := by
    have h := P.outer_equivariance 1 a 0 operadTwoSwap
    rw [operadTwoSwap_zero] at h
    exact h
  have hmove : (t ▷ V) ≫ (c ▷ V) = (c ▷ V) ≫ (t' ▷ V) := by
    have h := congrArg (· ▷ V) (P.arity_permutation_index_eq
      (by omega : 1 + a = (0 + a) + 1) (operadOuterPermutation 1 a 0 operadTwoSwap)).symm
    simp only [comp_whiskerRight] at h
    exact h
  have hsecond : (t' ▷ V) ≫ g₀ = g₁ ≫ w := by
    have h := P.outer_equivariance (0 + a) b ⟨a, by omega⟩ (operadTwoSwapAfterFirst a)
    rw [operadTwoSwapAfterFirst_last] at h
    exact h
  have houtput : w ≫ v = u ≫ B := by
    have h := P.arity_map_permutation_transport
      (by omega : (0 + a) + b = a + b) (by omega : (0 + a) + b = b + a)
      (operadTwoSwapOutput a b)
    have he : ((finCongr (by omega : (0 + a) + b = a + b)).symm.trans
        ((operadTwoSwapOutput a b).trans (finCongr (by omega : (0 + a) + b = b + a)))) =
        operadBlockSwap a b := by
      exact (show _ = operadBinaryOutputSwap a b from rfl).trans (operadBinaryOutputSwap_eq a b)
    rw [he] at h
    exact h
  have hparallel : P.binaryComposition a b =
      (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ g₁ ≫ u := by
    have h := congrArg ((α_ C U V).inv ≫ ·) (P.binaryComposition_parallel a b)
    dsimp only [C, U, V] at h
    rw [Iso.inv_hom_id_assoc] at h
    exact h
  have hf : (((A₀ ▷ U) ≫ f₁) ▷ V) = (f₀ ▷ V) ≫ (t ▷ V) :=
    (congrArg (· ▷ V) hfirst).trans (comp_whiskerRight f₀ t V)
  have hm := congrArg (· ≫ g₀ ≫ v) hmove
  simp only [Category.assoc] at hm
  have hs := congrArg (· ≫ v) hsecond
  simp only [Category.assoc] at hs
  calc
    _ = (α_ C U V).inv ≫ (((A₀ ▷ U) ≫ f₁) ▷ V) ≫ (c ▷ V) ≫ g₀ ≫ v :=
      tensorSubstitutionStep_swap A₀ f₁ ((c ▷ V) ≫ g₀ ≫ v)
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (t ▷ V) ≫ (c ▷ V) ≫ g₀ ≫ v := by
      rw [hf, Category.assoc]
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ (t' ▷ V) ≫ g₀ ≫ v := by rw [hm]
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ g₁ ≫ u ≫ B := by rw [hs, houtput]
    _ = _ := by simpa only [Category.assoc] using (congrArg (· ≫ B) hparallel).symm

end SerrePositivity.EInfinity.Operad
