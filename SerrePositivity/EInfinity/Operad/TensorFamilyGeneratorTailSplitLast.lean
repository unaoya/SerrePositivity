module

public import SerrePositivity.EInfinity.Operad.TensorFamilyGeneratorSplitLast
public import SerrePositivity.EInfinity.Operad.TensorPowerLastInput

/-!
# 未処理の末尾を含む有限作用族の最後の分離

概要：Berger–Moerdijk §1 の有限作用族の最後の作用を、未処理の末尾入力とともに取り出す。
方針：最後の分離の式を末尾とテンソルし、一次のブロックの単位因子を除く。
規約：前半、最後の作用の出力、末尾の順序を保つ。
使われ方：反復合成の評価の帰納段階で作用側の最後の演算を分離する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の作用と末尾を先にまとめてから前半の作用の出力を連結できる（Berger–Moerdijk §1）。
方針：最後の生成射の分離と、一次の出力の単位因子を除く連結の式を使う。
規約：入力族と末尾の長さは任意。
使われ方：代数で全合成を評価する帰納段階の右辺を最後の作用で分解する。 -/
lemma tensorFamilyGeneratorTail_splitLast_inv {ι : Type} (X : Complex A)
    (D : ι → Complex A) (e : ∀ i, D i ⟶ X) (n k : ℕ) (s : Fin (n + 1) → ι) :
    ((tensorFamilySplitLast n (fun j => D (s j))).inv ▷ power X k) ≫
      (tensorFamilyGenerator X D e (n + 1) s ⊗ₘ 𝟙 (power X k)) ≫
      (appendIso X (n + 1) k).hom =
    (α_ (tensorFamily n (fun j => D (s j.castSucc))) (D (s (Fin.last n))) (power X k)).hom ≫
      (tensorFamilyGenerator X D e n (fun j => s j.castSucc) ⊗ₘ
        (e (s (Fin.last n)) ▷ power X k)) ≫ (appendIso X n (k + 1)).hom ≫
      eqToHom (congrArg (power X) (by omega : n + (k + 1) = n + 1 + k)) := by
  rw [tensorHom_id, ← comp_whiskerRight_assoc, tensorFamilyGenerator_splitLast_inv]
  simp only [comp_whiskerRight, Category.assoc]
  rw [appendIso_lastInput]
  have h := associator_naturality
    (tensorFamilyGenerator X D e n (fun j => s j.castSucc))
    (e (s (Fin.last n))) (𝟙 (power X k))
  simp only [tensorHom_id] at h
  rw [reassoc_of% h]

end SerrePositivity.EInfinity
