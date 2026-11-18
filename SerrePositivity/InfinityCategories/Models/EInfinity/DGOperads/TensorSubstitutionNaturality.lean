module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitNaturality

/-!
模型。文献の定義との比較は後で
# 最後の演算を先に代入するテンソル射の等変性

概要：Berger–Moerdijk §1 の部分合成の反復で使うテンソル射の等変性を示す。
方針：最後の因子を係数の直後へ Koszul 交換し、二つの合成射の等変性を順に使う。
規約：ここでは複体と射についての一般補題を述べ、オペラッドの追加構造を仮定しない。
使われ方：全入力へのオペラッド合成の等変性の帰納段階でモノイダル計算を処理する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：最後の係数を先に代入して残りの演算を合成するテンソル射（Berger–Moerdijk §1）。
方針：二つの内側因子を交換してから、先の代入と残りの合成を適用する。
規約：交換には既存の Koszul 対称性を用いる。
使われ方：全入力への合成の再帰の一段を一般の複体射として表す。 -/
def tensorSubstitutionStep {R V L R' O : Complex A} (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) :
    R ⊗ (V ⊗ L) ⟶ O :=
  (R ◁ (β_ V L).hom) ≫ (α_ R L V).inv ≫ (f ▷ V) ≫ g

/-- 概要：二つの合成射の等変性は、最後の係数を先に代入する射の等変性を与える（Berger–Moerdijk §1）。
方針：対称性と結合子の自然性で因子ごとの射を合成射の前へ移す。
規約：各因子と中間対象の自己射は任意でよい。
使われ方：部分合成の同時等変性と再帰呼び出しの等変性を結び付ける。 -/
lemma tensorSubstitutionStep_equivariance {R V L R' O : Complex A}
    (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O)
    (a : R ⟶ R) (b : V ⟶ V) (c : L ⟶ L) (d : R' ⟶ R') (e : O ⟶ O)
    (hf : (a ⊗ₘ c) ≫ f = f ≫ d) (hg : (d ⊗ₘ b) ≫ g = g ≫ e) :
    (a ⊗ₘ (b ⊗ₘ c)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g ≫ e := by
  have hb : (a ⊗ₘ (b ⊗ₘ c)) ≫ (R ◁ (β_ V L).hom) =
      (R ◁ (β_ V L).hom) ≫ (a ⊗ₘ (c ⊗ₘ b)) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [BraidedCategory.braiding_naturality]
  have hfg : (((a ⊗ₘ c) ⊗ₘ b) ≫ (f ▷ V)) ≫ g = ((f ▷ V) ≫ (d ⊗ₘ b)) ≫ g := by
    congr 1
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hf]
  simp only [Category.assoc] at hfg
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← Category.assoc _ _ ((α_ R L V).inv ≫ (f ▷ V) ≫ g), hb]
  simp only [Category.assoc]
  rw [associator_inv_naturality_assoc, hfg, hg]

/-- 概要：有限族の最後の演算を分離してから代入する射（Berger–Moerdijk §1）。
方針：最後の因子を分離する同型に、二段の代入のテンソル射を合成する。
規約：残りの演算は元の順序を保つ。
使われ方：全入力へのオペラッド合成の再帰の一段を記述する。 -/
def tensorFamilySubstitutionStep (n : ℕ) {R R' O : Complex A}
    (V : Fin (n + 1) → Complex A) (f : R ⊗ V (Fin.last n) ⟶ R')
    (g : R' ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ O) :
    R ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V ⟶ O :=
  (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g

/-- 概要：各入力の自己射と二つの合成射の等変性から有限族の代入の等変性を得る（Berger–Moerdijk §1）。
方針：最後の因子の分離の自然性に、二段の代入の等変性を合成する。
規約：最後の因子と残りの有限族の射を別々に用いる。
使われ方：部分合成の等変性と帰納仮定を全入力への合成へ適用する。 -/
lemma tensorFamilySubstitutionStep_equivariance (n : ℕ) {R R' O : Complex A}
    (V : Fin (n + 1) → Complex A) (f : R ⊗ V (Fin.last n) ⟶ R')
    (g : R' ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ O)
    (a : R ⟶ R) (b : ∀ i, V i ⟶ V i) (d : R' ⟶ R') (e : O ⟶ O)
    (hf : (a ⊗ₘ b (Fin.last n)) ≫ f = f ≫ d)
    (hg : (d ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => b i.castSucc)) ≫ g = g ≫ e) :
    (a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) b) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V f g =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V f g ≫ e := by
  have hs : (a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) b) ≫
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom) ≫
        (a ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => b i.castSucc) ⊗ₘ b (Fin.last n))) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_naturality]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep
  rw [← Category.assoc, hs, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_equivariance f g a
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => b i.castSucc)) (b (Fin.last n)) d e hf hg]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
