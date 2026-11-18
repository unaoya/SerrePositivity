module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ComplexComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TensorEpimorphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexUnitLaws

/-!
模型。文献の定義との比較は後で
# 三因子の TR 比較と部分合成のテンソル自然性

概要：Berger–Fresse §1.3 の全射 TR から複体射の結合則を移す比較を用意する。
方針：二因子の可換正方形を左右のテンソルへ延長し、三重テンソルの全射性を使う。
規約：因子の cofibrancy や平坦性を仮定しない。
使われ方：χ の入れ子・並列結合則の消去と比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：左括弧の三因子 TR は全射（BF §1.3.4）。
方針：各成分と二因子テンソルの全射性を局所的に組み合わせる。
規約：arity は全て零を含む。
使われ方：χ の結合則を BE の結合則へ戻す。 -/
lemma triple_cochainMap_epi (m n k : ℕ) :
    Epi ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k) := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_cochainMap_epi A m n
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_epi A k
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_epi_of_epi A _ _

/-- 概要：双線形合成の可換正方形は右のテンソル因子を加えても可換（BF §1.3）。
方針：テンソル射の合成を二因子の合成へ分解する。
規約：任意の整数加群複体の射について成立する。
使われ方：χ の二回合成の第一段階を TR と交換する。 -/
lemma tensor_square_right {P Q R T P' Q' R' T' : Complex A}
    (f : P ⊗ Q ⟶ R) (g : P' ⊗ Q' ⟶ R') (a : P ⟶ P') (b : Q ⟶ Q')
    (c : R ⟶ R') (d : T ⟶ T') (h : f ≫ c = (a ⊗ₘ b) ≫ g) :
    ((a ⊗ₘ b) ⊗ₘ d) ≫ (g ▷ T') = (f ▷ T) ≫ (c ⊗ₘ d) := by
  change ((a ⊗ₘ b) ⊗ₘ d) ≫ (g ⊗ₘ 𝟙 _) = (f ⊗ₘ 𝟙 _) ≫ (c ⊗ₘ d)
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [h]

/-- 概要：双線形合成の可換正方形は左のテンソル因子を加えても可換（BF §1.3）。
方針：テンソル射の合成則と与えられた可換性を使う。
規約：単位や次数の条件を追加しない。
使われ方：入れ子合成の右辺の内側合成を TR と交換する。 -/
lemma tensor_square_left {P Q R T P' Q' R' T' : Complex A}
    (f : Q ⊗ R ⟶ T) (g : Q' ⊗ R' ⟶ T') (a : P ⟶ P') (b : Q ⟶ Q')
    (c : R ⟶ R') (d : T ⟶ T') (h : f ≫ d = (b ⊗ₘ c) ≫ g) :
    (a ⊗ₘ (b ⊗ₘ c)) ≫ (P' ◁ g) = (P ◁ f) ≫ (a ⊗ₘ d) := by
  change (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 _ ⊗ₘ g) = (𝟙 _ ⊗ₘ f) ≫ (a ⊗ₘ d)
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [h]

/-- 概要：arity の等式の射を含む二因子 TR の正方形は可換（BF §1.3）。
方針：arity 等式を消去する。
規約：右の因子は任意の arity で固定する。
使われ方：並列合成の第一段階の出力 arity の括弧を移す。 -/
lemma tensor_cochainMap_arity {m n : ℕ} (h : m = n) (k : ℕ) :
    eqToHom (congrArg (fun q => _root_.SerrePositivity.EInfinity.BarrattEccles.complex A q ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A k) h) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A k) ≫
        eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A q ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A k) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
