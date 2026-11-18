module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAfterTwoFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoSlotSubstitutionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyLastSwapOuter

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.twoSlotComposition

/-- 概要：末尾交換の後の分離と反復合成は、元の分離と反復合成の後の尾の交換に一致する（Berger–Moerdijk §1）。
方針：分離同型の外側の係数射を伴う可換性に、二位置への合成と残りの代入の等変性を合成する。
規約：交換後の分離の終域を元の前半と交換した末尾二因子へ移す。
使われ方：arity の移送を含む全入力への合成の外側等変性の中心の式を与える。 -/
lemma composeFirstInputs_lastSwap_separated (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    let R := P.arity ((n + k) + 2)
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + k) + 2)
        (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun i => P.arity (s i)) (Fin.last n)).hom) ≫
        (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n
          (fun i => P.arity (s (adjacentTransposition (Fin.last n) i)))).hom) ≫
        (R ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n (fun i => P.arity (s i)))) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) b a ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k b a (fun i => s i.castSucc.castSucc)) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n (fun i => P.arity (s i))).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k a b (fun i => s i.castSucc.castSucc)) ≫
        P.arityBijectionMap (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (Equiv.refl (Fin (∑ i : Fin n, s i.castSucc.castSucc)))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k a b)) := by
  dsimp only
  have hout := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_lastSwap_outer n (fun i => P.arity (s i))
    (R := P.arity ((n + k) + 2))
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + k) + 2)
      (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)))
  have h := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
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

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
