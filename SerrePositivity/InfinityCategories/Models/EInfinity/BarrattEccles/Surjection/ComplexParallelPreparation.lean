module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompositionNaturality
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionInsertion
public import SerrePositivity.EInfinity.BarrattEccles.ParallelTensor

/-!
模型。文献の定義との比較は後で
# 並列合成の出力移送と因子交換の比較

概要：Berger–Fresse §1.2.4–5 の並列結合則で使う arity 移送と三因子交換を整える。
方針：最初の代入後に arity の括弧を直し、TR と結合子・交換子の自然性を使う。
規約：交換は既存の Koszul braiding による。
使われ方：χ の複体射の並列結合則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：最後の二因子交換は三つの複体射に関して自然（BF §1.2.4–5）。
方針：結合子の自然性・交換子の自然性・逆結合子の自然性を順に使う。
規約：任意の整数加群複体に適用できる。
使われ方：三重テンソル TR を並列結合則の因子交換の前後へ移す。 -/
@[reassoc] lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.exchangeLastFactors_naturality
    {P Q T P' Q' T' : Complex A} (a : P ⟶ P') (b : Q ⟶ Q') (c : T ⟶ T') :
    ((a ⊗ₘ b) ⊗ₘ c) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.exchangeLastFactors P' Q' T' =
      _root_.SerrePositivity.EInfinity.BarrattEccles.exchangeLastFactors P Q T ≫ ((a ⊗ₘ c) ⊗ₘ b) := by
  have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_square_left A (β_ Q T).hom (β_ Q' T').hom a b c
    (c ⊗ₘ b) (CategoryTheory.BraidedCategory.braiding_naturality b c).symm
  simp only [_root_.SerrePositivity.EInfinity.BarrattEccles.exchangeLastFactors, Category.assoc]
  rw [associator_naturality_assoc, reassoc_of% hh, associator_inv_naturality]

namespace Surjection

/-- 概要：並列代入の一回目の出力 arity の括弧を直す（BF §1.2.4–5）。
方針：構成した部分合成射に等式の射を合成する。
規約：次の外側 arity は m+n+1。
使われ方：並列合成の二段目を型付けする。 -/
def _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexCompositionAfterInsertion (m n : ℕ) (i : Fin (m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 2) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A (m + 1) n i ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (by omega : m + 1 + n = m + n + 1))

/-- 概要：TR は最初の並列代入と出力 arity の移送を保つ（BF §1.3）。
方針：arity の等式の自然性と既存の合成保存を連結する。
規約：内側 arity 零を含む。
使われ方：並列結合則の両辺を全射 TR で比較する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexCompositionAfterInsertion_comm (m n : ℕ) (i : Fin (m + 2)) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.partialCompositionAfterInsertion A m n i ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n + 1) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 2) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexCompositionAfterInsertion A m n i := by
  simp only [_root_.SerrePositivity.EInfinity.BarrattEccles.partialCompositionAfterInsertion, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexCompositionAfterInsertion,
    Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_arity A (by omega : m + 1 + n = m + n + 1),
    reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A (m + 1) n i)]

/-- 概要：χ の arity 等式のテンソル移送は等式の射の右テンソル（BF §1.2.4–5）。
方針：arity 等式を消去する。
規約：右因子は任意の整数複体。
使われ方：並列の前向き結合則を Operad の公理の文言へ直す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.arity_tensor_eqToHom {m n : ℕ} (h : m = n) (T : Complex A) :
    eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A q ⊗ T) h) =
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) h) ▷ T := by
  cases h
  simp

end Surjection
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles
