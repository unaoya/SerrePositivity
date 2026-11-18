module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockArities
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionFirstBlock

/-!
模型。文献の定義との比較は後で
# 先頭ブロックの合成を外側の全合成へ戻す

概要：Berger–Moerdijk §1 の結合則の係数側で、まとめた先頭演算を外側の入力族へ組み込む。
方針：arity 族の等式で移送し、逆のテンソル分離と単位子で先頭演算を挿入する。
規約：総 arity は元の族 s の和へ統一する。
使われ方：Schur 作用の先頭での部分合成則の係数の計算を完結する。
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

/-- 概要：先頭分解を等しい先頭 arity と後半の族へ移送できる（Berger–Moerdijk §1）。
方針：先頭と後半の等式を消去し、単位因子を除いた先頭分解を適用する。
規約：移送は入力テンソル全体の等式で行う。
使われ方：まとめた先頭ブロックの入力族を元の前半と後半で表す。 -/
lemma composition_head_transport (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m : ℕ) (u : Fin (1 + m) → ℕ)
    (q : ℕ) (t : Fin m → ℕ) (hq : q = u ((0 : Fin 1).castAdd m))
    (ht : t = fun j => u (j.natAdd 1)) (e : q + (∑ j, t j) = ∑ j, u j) :
    (P.arity (1 + m) ◁
      (eqToHom (by rw [hq, ht] :
        P.arity q ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (t j)) =
        P.arity (u ((0 : Fin 1).castAdd m)) ⊗
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (u (j.natAdd 1)))) ≫
      ((ρ_ (P.arity (u ((0 : Fin 1).castAdd m)))).inv ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (u (j.natAdd 1)))) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt 1 m (fun j => P.arity (u j))).inv)) ≫
      P.composition (1 + m) u =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 t)
      (P.composeAheadOfInputs (∑ j, t j) 0 q) ≫ eqToHom (congrArg P.arity e) := by
  subst q
  subst t
  simpa only [eqToHom_refl, Category.id_comp] using P.composition_head_without_unit m u

/-- 概要：まとめた先頭演算と後半の演算族を外側の入力テンソルへ組み込む（Berger–Moerdijk §1）。
方針：先頭と後半の arity の同定、単位因子の挿入、逆のテンソル分離を合成する。
規約：入力の順序は先頭演算、その後に元の後半の演算族。
使われ方：内側の全合成の結果を外側の全合成へ渡す。 -/
def firstBlockAssembly (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.arity (∑ j : Fin n, s (j.castAdd m)) ⊗
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))) ⟶
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j)) :=
  eqToHom (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_head, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_tail] :
    P.arity (∑ j : Fin n, s (j.castAdd m)) ⊗
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))) =
    P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s ((0 : Fin 1).castAdd m)) ⊗
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s (j.natAdd 1)))) ≫
    ((ρ_ (P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s ((0 : Fin 1).castAdd m)))).inv ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s (j.natAdd 1)))) ≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt 1 m (fun j => P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j))).inv

/-- 概要：まとめた先頭演算を組み込んだ全合成は後半と先頭への二段の合成に一致する（Berger–Moerdijk §1）。
方針：単位因子を除いた先頭分解を適用し、入力族と総和の移送を整理する。
規約：最後に元の入力族 s の総 arity へ戻す。
使われ方：先頭ブロックの全合成と外側の全合成を結び付ける。 -/
lemma firstBlockAssembly_composition (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (P.arity (1 + m) ◁ P.firstBlockAssembly n m s) ≫
      P.composition (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) ≫
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 (fun j => s (j.natAdd n)))
      (P.composeAheadOfInputs (∑ j : Fin m, s (j.natAdd n)) 0
        (∑ j : Fin n, s (j.castAdd m))) ≫
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm) := by
  have h := P.composition_head_transport m (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)
    (∑ j : Fin n, s (j.castAdd m)) (fun j => s (j.natAdd n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_head n m s).symm
    (funext fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_tail n m s j).symm)
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm)
  have h' := congrArg (· ≫ eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s))) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.firstBlockAssembly, Category.assoc, eqToHom_trans] using h'

/-- 概要：内側の演算と全入力族から外側の入力族への射（Berger–Moerdijk §1）。
方針：前半と後半を分離し、前半へ全合成を適用してからまとめた先頭演算を組み込む。
規約：後半の演算族には恒等射を作用させる。
使われ方：先頭での部分合成と全合成の結合則の右辺を構成する。 -/
def firstBlockCompositionInputs (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.arity n ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j)) :=
  (P.arity n ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => P.arity (s j))).hom) ≫
    (α_ (P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m))))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))).inv ≫
    (P.composition n (fun j => s (j.castAdd m)) ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n)))) ≫
    P.firstBlockAssembly n m s

/-- 概要：先頭への部分合成と全入力への合成は内側と外側の二段の全合成に一致する（Berger–Moerdijk §1）。
方針：二ブロック分解の結合則と、まとめた先頭演算を外側へ組み込む式を結ぶ。
規約：先頭 n 入力をまとめ、最後に元の入力族の総 arity へ移送する。
使われ方：自由代数の先頭での部分合成則に必要なオペラッド係数の結合則。 -/
lemma composition_first_block_assoc (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j))) ≫
      P.composition (n + m) s =
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j)))).hom ≫
      (P.arity (1 + m) ◁ P.firstBlockCompositionInputs n m s) ≫
      P.composition (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) ≫
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s)) := by
  rw [P.composition_after_first_block m n s]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.firstBlockCompositionInputs
  simp only [whiskerLeft_comp, Category.assoc]
  conv_rhs =>
    arg 2
    arg 2
    arg 2
    arg 2
    erw [P.firstBlockAssembly_composition n m s]
  rw [associator_naturality_right_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
