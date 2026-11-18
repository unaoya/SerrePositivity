module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentSplitLast
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PrefixInsertionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionSquares

/-!
模型。文献の定義との比較は後で
# 隣接交換に関する反復合成の帰納段階

概要：Berger–Moerdijk §1 の末尾固定の隣接交換の外側等変性を前半の反復合成から導く。
方針：最初の代入と前半の反復合成の正方形を接続し、分離と入力データの移送を前後に合成する。
規約：最後の指定入力の arity を未代入の尾へ加える。
使われ方：反復合成の任意の隣接交換の外側等変性の帰納法に用いる。
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
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion

/-- 概要：前半の反復合成の外側等変性から一段の代入射の外側等変性を得る（Berger–Moerdijk §1）。
方針：最初の代入の等変性と前半の等変性の正方形へテンソル代入の自然性を適用する。
規約：前半の出力の全単射 e を明示する。
使われ方：隣接交換の帰納段階で分離後の二つの合成射を比較する。 -/
lemma composeFirstInputs_adjacent_step_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n)
    (e : Fin ((∑ j : Fin (n + 1), s j.castSucc) + (k + s (Fin.last (n + 1)))) ≃
      Fin ((∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1)))))
    (hprefix :
      (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + 1) + (k + s (Fin.last (n + 1))))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i)
            (Equiv.refl (Fin (k + s (Fin.last (n + 1))))))) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j.castSucc)) i).hom) ≫
          P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1)))
            (fun j => s (adjacentTransposition i j).castSucc) =
        P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) ≫
          P.arityBijectionMap e) :
    let l := s (Fin.last (n + 1))
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i.castSucc) (Equiv.refl (Fin k)))) ⊗ₘ
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j.castSucc)) i).hom ⊗ₘ 𝟙 (P.arity l))) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
          (P.composeFirstInputs (n + 1) (k + l)
            (fun j => s (adjacentTransposition i j).castSucc)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
        (P.composeFirstInputs (n + 1) (k + l) (fun j => s j.castSucc)) ≫ P.arityBijectionMap e := by
  dsimp only
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_naturality _ _ _ _ _ _ _
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + 1) + (k + s (Fin.last (n + 1))))
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i)
        (Equiv.refl (Fin (k + s (Fin.last (n + 1)))))))) _ ?_ hprefix
  rw [tensorHom_id]
  exact P.composeFirstInputInsertion_adjacent_prefix_equivariance n k
    (s (Fin.last (n + 1))) i

/-- 概要：前半の等変性から末尾固定の隣接交換の分離後の等変性を得る（Berger–Moerdijk §1）。
方針：外側の係数射を伴う分離の可換性に一段の代入射の等変性を合成する。
規約：出力は前半の反復合成の後の arity のまま比較する。
使われ方：元の反復合成へ終域の移送を合成する前の式を与える。 -/
lemma composeFirstInputs_adjacent_separated (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n)
    (e : Fin ((∑ j : Fin (n + 1), s j.castSucc) + (k + s (Fin.last (n + 1)))) ≃
      Fin ((∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1)))))
    (hprefix :
      (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + 1) + (k + s (Fin.last (n + 1))))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i)
            (Equiv.refl (Fin (k + s (Fin.last (n + 1))))))) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j.castSucc)) i).hom) ≫
          P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1)))
            (fun j => s (adjacentTransposition i j).castSucc) =
        P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) ≫
          P.arityBijectionMap e) :
    let l := s (Fin.last (n + 1))
    let R := P.arity (n + 2 + k)
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i.castSucc) (Equiv.refl (Fin k)))) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun j => P.arity (s j)) i.castSucc).hom) ≫
        (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1)
          (fun j => P.arity (s (adjacentTransposition i.castSucc j)))).hom) ≫
        (R ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj n (fun j => P.arity (s j)) i)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
          (P.composeFirstInputs (n + 1) (k + l)
            (fun j => s (adjacentTransposition i j).castSucc)) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) (fun j => P.arity (s j))).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
          (P.composeFirstInputs (n + 1) (k + l) (fun j => s j.castSucc)) ≫
        P.arityBijectionMap e := by
  dsimp only
  have hout := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_adjacent_outer n (fun j => P.arity (s j)) i
    (R := P.arity (n + 2 + k))
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i.castSucc) (Equiv.refl (Fin k)))))
  have h := congrArg (fun f => f ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k (s (Fin.last (n + 1))))
      (P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1)))
        (fun j => s (adjacentTransposition i j).castSucc))) hout
  simp only [Category.assoc] at h
  conv_rhs at h =>
    arg 2
    rw [P.composeFirstInputs_adjacent_step_equivariance n k s i e hprefix]
  exact h

/-- 概要：前半の等変性から元の反復合成の末尾固定の隣接交換の等変性を得る（Berger–Moerdijk §1）。
方針：交換前後の因子分解と分離後の等変性を組み合わせ、終域の移送を相殺する。
規約：前半の出力の全単射 e を全入力の和の間へ移して作用させる。
使われ方：反復合成の任意の隣接交換の外側等変性の帰納段階に直接適用する。 -/
lemma composeFirstInputs_adjacent_cast_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n)
    (e : Fin ((∑ j : Fin (n + 1), s j.castSucc) + (k + s (Fin.last (n + 1)))) ≃
      Fin ((∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1)))))
    (hprefix :
      (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + 1) + (k + s (Fin.last (n + 1))))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i)
            (Equiv.refl (Fin (k + s (Fin.last (n + 1))))))) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j.castSucc)) i).hom) ≫
          P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1)))
            (fun j => s (adjacentTransposition i j).castSucc) =
        P.composeFirstInputs (n + 1) (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) ≫
          P.arityBijectionMap e) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i.castSucc) (Equiv.refl (Fin k)))) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun j => P.arity (s j)) i.castSucc).hom) ≫
        P.composeFirstInputs (n + 2) k (fun j => s (adjacentTransposition i.castSucc j)) =
      P.composeFirstInputs (n + 2) k s ≫
        P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentCastOutput n k s i e) := by
  have h := congrArg (· ≫ eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotSwapOutput_eq n k s i)))
    (P.composeFirstInputs_adjacent_separated n k s i e hprefix)
  simp only [Category.assoc] at h
  conv_lhs =>
    arg 2
    rw [P.composeFirstInputs_adjacent_cast_factor n k s i]
  conv_rhs =>
    arg 1
    rw [P.composeFirstInputs_oneSlot_after_factor (n + 1) k s]
  conv_rhs =>
    arg 2
    rw [P.arity_adjacentCastOutput n k s i e]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
