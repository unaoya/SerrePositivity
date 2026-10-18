module

public import SerrePositivity.EInfinity.Operad.CompositionAfterTwoFactor
public import SerrePositivity.EInfinity.Operad.TwoSlotSubstitutionEquivariance
public import SerrePositivity.EInfinity.Operad.TensorFamilyLastSwapOuter

/-!
# 末尾二入力の交換に対する分離と反復合成の両立

概要：Berger–Moerdijk §1 の末尾二入力の外側交換を分離同型と二位置への合成の等変性で計算する。
方針：外側の係数射を伴う分離の可換性の後に、二位置への合成と残りの代入の等変性を適用する。
規約：外側の arity は (n+k)+2、尾の長さの表記は (k+a)+b とする。
使われ方：全入力への反復合成の外側等変性で末尾二入力を交換する段階へ用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  tensorSubstitutionStep composeFirstInputsAfterTwo twoSlotComposition

/-- 概要：末尾交換の後の分離と反復合成は、元の分離と反復合成の後の尾の交換に一致する（Berger–Moerdijk §1）。
方針：分離同型の外側の係数射を伴う可換性に、二位置への合成と残りの代入の等変性を合成する。
規約：交換後の分離の終域を元の前半と交換した末尾二因子へ移す。
使われ方：arity の移送を含む全入力への合成の外側等変性の中心の式を与える。 -/
lemma composeFirstInputs_lastSwap_separated (P : Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    let R := P.arity ((n + k) + 2)
    (P.sequence.map (FiniteBijection.permutation ((n + k) + 2)
        (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)) ⊗ₘ
      (tensorFamilyAdjacentIso (n + 1) (fun i => P.arity (s i)) (Fin.last n)).hom) ≫
        (R ◁ (tensorFamilySplitLastTwo n
          (fun i => P.arity (s (adjacentTransposition (Fin.last n) i)))).hom) ≫
        (R ◁ eqToHom (tensorFamily_lastSwap_output_obj n (fun i => P.arity (s i)))) ≫
        tensorSubstitutionStep
          (P.twoSlotComposition (n + k) b a ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k b a (fun i => s i.castSucc.castSucc)) =
      (R ◁ (tensorFamilySplitLastTwo n (fun i => P.arity (s i))).hom) ≫
        tensorSubstitutionStep
          (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k a b (fun i => s i.castSucc.castSucc)) ≫
        P.arityBijectionMap (FiniteBijection.blockEquiv
          (Equiv.refl (Fin (∑ i : Fin n, s i.castSucc.castSucc)))
          (operadTailBlockSwap k a b)) := by
  dsimp only
  have hout := tensorFamilySplitLastTwo_lastSwap_outer n (fun i => P.arity (s i))
    (R := P.arity ((n + k) + 2))
    (P.sequence.map (FiniteBijection.permutation ((n + k) + 2)
      (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)))
  have h := congrArg (fun f => f ≫ tensorSubstitutionStep
    (P.twoSlotComposition (n + k) (s (Fin.last (n + 1))) (s (Fin.last n).castSucc)
      ⟨n, by omega⟩ ⟨n + 1, by omega⟩ (by change n < n + 1; omega))
    (P.composeFirstInputsAfterTwo n k (s (Fin.last (n + 1))) (s (Fin.last n).castSucc)
      (fun i => s i.castSucc.castSucc))) hout
  simp only [Category.assoc] at h
  conv_rhs at h =>
    arg 2
    rw [P.twoSlotSubstitution_adjacent_equivariance n k
      (s (Fin.last n).castSucc) (s (Fin.last (n + 1))) (fun i => s i.castSucc.castSucc)]
  exact h

end SerrePositivity.EInfinity.Operad
