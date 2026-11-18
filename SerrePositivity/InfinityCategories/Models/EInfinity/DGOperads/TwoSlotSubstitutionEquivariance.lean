module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAfterTwoSlots
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionSquares

/-!
模型。文献の定義との比較は後で
# 二位置への合成と残りの代入の外側等変性

概要：Berger–Moerdijk §1 の隣接二入力への合成と残りの反復合成の可換正方形を接続する。
方針：異なる対象間のテンソル代入の自然性を二つの外側等変性に適用する。
規約：前半の入力族と未代入の尾 k 個を保ち、二入力の arity a,b の順序を交換する。
使われ方：末尾二入力の交換に関する全入力への合成の外側等変性を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.twoSlotComposition

/-- 概要：隣接二入力への合成と残りの反復合成の代入射は外側交換と両立する（Berger–Moerdijk §1）。
方針：二位置への合成の等変性と残りの合成の尾の等変性にテンソル代入の自然性を適用する。
規約：前半の有限テンソルの射は恒等とし、二入力の対に対称性を作用させる。
使われ方：分離同型を含む末尾交換の可換性へ接続する中心の合成射を与える。 -/
lemma twoSlotSubstitution_adjacent_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k a b : ℕ)
    (s : Fin n → ℕ) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + k) + 2)
        (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)) ⊗ₘ
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ⊗ₘ
        (β_ (P.arity a) (P.arity b)).hom)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) b a ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k b a s) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
        (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by change n < n + 1; omega))
        (P.composeFirstInputsAfterTwo n k a b s) ≫
        P.arityBijectionMap (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (Equiv.refl (Fin (∑ i, s i))) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k a b)) := by
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_naturality _ _ _ _ _ _ _
    (P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap n k a b)) _ ?_ ?_
  · exact P.twoSlotComposition_adjacent_equivariance n k a b
  · rw [tensorHom_id]
    exact P.composeFirstInputsAfterTwo_equivariance n k a b s

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
