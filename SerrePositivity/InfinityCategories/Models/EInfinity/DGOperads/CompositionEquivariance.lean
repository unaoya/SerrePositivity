module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotTailPermutations

/-!
模型。文献の定義との比較は後で
# 部分合成の同時等変性と未代入の入力

概要：Berger–Moerdijk §1 の内側・外側の等変性を同時に適用する計算則を証明する。
方針：係数の二つの置換を分離して適用し、出力の置換を挿入区間のブロック置換と同定する。
規約：置換の積と圏の射の合成の順序を区別する。arity 0 の挿入を含む。
使われ方：全入力への合成の等変性で、代入後の尾の置換を次の帰納段階へ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

private lemma tensor_comp_equivariance {X Y Z : Complex A} (f g : X ⊗ Y ⟶ Z)
    (a : X ⟶ X) (b : Y ⟶ Y) (c d : Z ⟶ Z)
    (ha : (a ▷ Y) ≫ g = f ≫ d) (hb : (X ◁ b) ≫ f = f ≫ c) :
    (a ⊗ₘ b) ≫ g = f ≫ c ≫ d := by
  rw [tensorHom_def', Category.assoc, ha, ← Category.assoc, hb, Category.assoc]

/-- 概要：部分合成は内側と外側の置換の同時適用と両立する（Berger–Moerdijk §1）。
方針：テンソル射を二つの whisker に分け、外側と内側の等変性を順に適用する。
規約：出力では内側置換の後に外側置換を適用する。
使われ方：全入力への合成の等変性を部分合成の等変性から導く。 -/
lemma comp_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ⊗ₘ
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n τ)) ≫ P.comp m n (σ i) =
        P.comp m n i ≫ P.sequence.map
          (_root_.SerrePositivity.FiniteBijection.permutation (m + n)
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ))) := by
  calc
    _ = P.comp m n i ≫
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ)) ≫
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.tensor_comp_equivariance (P.comp m n i) (P.comp m n (σ i)) _ _ _ _
        (P.outer_equivariance m n i σ) (P.inner_equivariance m n i τ)
    _ = _ := by
      rw [← Equiv.Perm.mul_def, _root_.SerrePositivity.FiniteBijection.permutation_mul, P.sequence.map_comp]

/-- 概要：前方を固定する外側置換と内側置換は代入後の尾のブロック置換になる（Berger–Moerdijk §1）。
方針：部分合成の同時等変性に、挿入位置の固定と三つのブロックの置換の同定を適用する。
規約：先頭 a 個の入力を未処理とし、位置 a に l 入力の演算を代入する。
使われ方：全入力への合成の内側等変性の帰納段階に用いる。 -/
lemma comp_tail_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b l : ℕ)
    (τ : Equiv.Perm (Fin l)) (ρ : Equiv.Perm (Fin b)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ)) ⊗ₘ
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation l τ)) ≫ P.comp (a + b) l ⟨a, by omega⟩ =
        P.comp (a + b) l ⟨a, by omega⟩ ≫ P.sequence.map
          (_root_.SerrePositivity.FiniteBijection.permutation (a + b + l) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation a b l τ ρ)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_slot, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_tail_outer] using
    P.comp_equivariance (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ) τ

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
