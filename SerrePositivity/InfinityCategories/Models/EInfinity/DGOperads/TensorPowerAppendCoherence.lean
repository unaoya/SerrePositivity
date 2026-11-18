module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerSeparation

/-!
模型。文献の定義との比較は後で
# 二列への分離とブロック連結の整合性

概要：Berger–Fresse §3.1 の反復評価のブロック分解に必要なモノイダル図式を扱う。
方針：連結の零段と帰納段を単位子・結合子・tensorμ の自然性に帰着する。
規約：対象の射は任意であり、次数や同型性を仮定しない。
使われ方：テンソル冪の分離と二つのブロックの連結の両立を証明する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.TensorPowers

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：空の前半ブロックの分離は左単位子と両立する（BF §3.1）。
方針：tensorμ の自然性とテンソル関手の左単位則を使う。
規約：後半の分離射は任意の射でよい。
使われ方：ブロック連結の両立の帰納法の零段となる。 -/
lemma tensorSeparation_appendZero {N R S : C} (s : N ⟶ R ⊗ S) :
    (λ_ N).hom ≫ s =
      ((λ_ (𝟙_ C)).inv ⊗ₘ s) ≫ tensorμ (𝟙_ C) (𝟙_ C) R S ≫
        ((λ_ R).hom ⊗ₘ (λ_ S).hom) := by
  rw [tensorHom_def', Category.assoc]
  rw [← tensor_left_unitality]
  exact (leftUnitor_naturality s).symm

/-- 概要：前半に一対を追加したブロック連結の分離図式（BF §3.1）。
方針：分離射を結合子へ通し、tensorμ の結合則と自然性を適用する。
規約：前半・後半の分離と各列の連結を独立な射として持つ。
使われ方：テンソル冪の二列分離と連結の帰納段となる。 -/
lemma tensorSeparation_appendStep {V W N M R S T U L Q : C}
    (s : N ⟶ R ⊗ S) (t : M ⟶ T ⊗ U) (a : R ⊗ T ⟶ L) (b : S ⊗ U ⟶ Q) :
    (α_ (V ⊗ W) N M).hom ≫
      ((V ⊗ W) ◁ ((s ⊗ₘ t) ≫ tensorμ R S T U ≫ (a ⊗ₘ b))) ≫ tensorμ V W L Q =
    ((((V ⊗ W) ◁ s) ≫ tensorμ V W R S) ⊗ₘ t) ≫
      tensorμ (V ⊗ R) (W ⊗ S) T U ≫
      (((α_ V R T).hom ≫ (V ◁ a)) ⊗ₘ ((α_ W S U).hom ≫ (W ◁ b))) := by
  have hα := associator_naturality (𝟙 (V ⊗ W)) s t
  simp only [id_tensorHom] at hα
  have hf : ((((V ⊗ W) ◁ s) ≫ tensorμ V W R S) ⊗ₘ t) =
      (((V ⊗ W) ◁ s) ⊗ₘ t) ≫ (tensorμ V W R S ▷ (T ⊗ U)) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hα, tensorμ_natural_right, ← tensor_associativity_assoc, hf]
  simp only [Category.assoc, tensorHom_comp_tensorHom]

/-- 概要：同じ二因子を二回交換する分離は恒等射（BF §3.1）。
方針：対称性で逆の tensorδ を逆向きの tensorμ と同定して相殺する。
規約：四対象は独立でよい。
使われ方：連結と反復評価の比較で二回の分離を消す。 -/
@[reassoc]
lemma tensorSeparation_twice (V W R S : C) :
    tensorμ V W R S ≫ tensorμ V R W S = 𝟙 _ := by
  have hδ : tensorδ V W R S = tensorμ V R W S := by
    rw [tensorδ, tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding W R]
  rw [← hδ, tensorμ_tensorδ]

omit [SymmetricCategory C] in
/-- 概要：空ブロックの連結後の arity の移送を消去する（BF §3.1）。
方針：連結同型の定義の二つの逆向きの移送を相殺する。
規約：零重テンソルはテンソル単位である。
使われ方：二列分離の連結の零段で算術的な arity の差を消す。 -/
lemma tensorPowerAppend_zero_transport (V : C) (n : ℕ) :
    (appendIso V 0 n).hom ≫ eqToHom (congrArg (power V) (Nat.zero_add n)) =
      (λ_ (power V n)).hom := by
  change ((λ_ (power V n)).hom ≫
    eqToHom (congrArg (power V) (Nat.zero_add n).symm)) ≫
      eqToHom (congrArg (power V) (Nat.zero_add n)) = _
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

omit [SymmetricCategory C] in
/-- 概要：非空ブロックの連結後の arity の移送を消去する（BF §3.1）。
方針：連結同型の帰納定義の移送を相殺する。
規約：最初の因子を保ち、尾の二ブロックを連結する。
使われ方：二列分離とブロック連結の帰納段で算術的な表示を揃える。 -/
lemma tensorPowerAppend_succ_transport (V : C) (m n : ℕ) :
    (appendIso V (m + 1) n).hom ≫ eqToHom (congrArg (power V) (Nat.succ_add m n)) =
      (α_ V (power V m) (power V n)).hom ≫ (V ◁ (appendIso V m n).hom) := by
  simp only [appendIso, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
