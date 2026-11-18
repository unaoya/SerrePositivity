module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionUnit

/-!
模型。文献の定義との比較は後で
# 代入射の残りの入力についての自然性

概要：Berger–Moerdijk §1 の二入力への代入で、処理前の因子のテンソル単位を除く。
方針：代入する因子との交換の自然性を使い、残りの因子の射を代入の前へ移す。
規約：部分合成の係数と代入される因子は固定する。
使われ方：二入力の全合成を通常の部分合成の交換則に接続する。
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

/-- 概要：代入射は残りの入力因子の射について自然である（Berger–Moerdijk §1）。
方針：対称性と結合子の自然性を使い、入力の射を最初の部分合成の後へ移す。
規約：残りの入力の射は任意の複体射でよい。
使われ方：一つ残った演算のテンソル単位を代入の前に除く。 -/
lemma tensorSubstitutionStep_middle {R R' L V W O : Complex A}
    (f : R ⊗ L ⟶ R') (g : R' ⊗ W ⟶ O) (h : V ⟶ W) :
    (R ◁ (h ⊗ₘ 𝟙 L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((R' ◁ h) ≫ g) := by
  have hb : (h ⊗ₘ 𝟙 L) ≫ (β_ W L).hom = (β_ V L).hom ≫ (𝟙 L ⊗ₘ h) :=
    BraidedCategory.braiding_naturality h (𝟙 L)
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← whiskerLeft_comp_assoc, hb]
  simp only [whiskerLeft_comp, id_tensorHom, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]

/-- 概要：二因子の最後の分離は、前半の右単位子を除くと通常の右単位子に一致する（Berger–Moerdijk §1）。
方針：結合子と左右の単位子の整合性を用いる。
規約：入力族は二要素。
使われ方：二入力への全合成のテンソル単位を除く。 -/
lemma tensorFamilySplitLast_one_unit (V : Fin 2 → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast 1 V).hom ≫ ((ρ_ (V 0)).hom ⊗ₘ 𝟙 (V 1)) =
      V 0 ◁ (ρ_ (V 1)).hom := by
  change ((V 0 ◁ ((ρ_ (V 1)).hom ≫ (λ_ (V 1)).inv)) ≫
    (α_ (V 0) (𝟙_ (Complex A)) (V 1)).inv) ≫ ((ρ_ (V 0)).hom ⊗ₘ 𝟙 (V 1)) = _
  rw [Category.assoc, tensorHom_id]
  have hc : (α_ (V 0) (𝟙_ (Complex A)) (V 1)).inv ≫ ((ρ_ (V 0)).hom ▷ V 1) =
      V 0 ◁ (λ_ (V 1)).hom := by monoidal_coherence
  rw [hc, ← whiskerLeft_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：二つの入力への代入は、内側演算の末尾の単位を先に除いて計算できる（Berger–Moerdijk §1）。
方針：代入射の中間因子についての自然性と、二因子の分離の単位則を使う。
規約：一つ目の部分合成の後に残る一因子の単位を右単位子で除く。
使われ方：二入力の全合成を単位を持たない三因子の部分合成へ戻す。 -/
lemma tensorFamilySubstitutionStep_one {R R' O : Complex A} (V : Fin 2 → Complex A)
    (f : R ⊗ V (Fin.last 1) ⟶ R') (g : R' ⊗ V 0 ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep 1 V f ((R' ◁ (ρ_ (V 0)).hom) ≫ g) =
      (R ◁ (V 0 ◁ (ρ_ (V 1)).hom)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g := by
  change R ⊗ V 1 ⟶ R' at f
  have hm := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle f g (ρ_ (V 0)).hom).symm
  have hp : (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast 1 V).hom) ≫
      (R ◁ ((ρ_ (V 0)).hom ⊗ₘ 𝟙 (V 1))) = R ◁ (V 0 ◁ (ρ_ (V 1)).hom) :=
    (whiskerLeft_comp R _ _).symm.trans
      (congrArg (R ◁ ·) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_one_unit V))
  calc
    _ = (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast 1 V).hom) ≫
        (R ◁ ((ρ_ (V 0)).hom ⊗ₘ 𝟙 (V 1))) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g :=
      congrArg ((R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast 1 V).hom) ≫ ·) hm
    _ = _ := by rw [← Category.assoc, hp]

/-- 概要：代入の最初の係数射の後の射は残りの合成の前へ移せる（Berger–Moerdijk §1）。
方針：whisker が合成を保つことを使う。
規約：中間の複体の射は任意。
使われ方：最初の部分合成の後の arity の移送を残りの合成へまとめる。 -/
lemma tensorFamilySubstitutionStep_first_post (n : ℕ) {R R' R'' O : Complex A}
    (V : Fin (n + 1) → Complex A) (f : R ⊗ V (Fin.last n) ⟶ R') (t : R' ⟶ R'')
    (g : R'' ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V (f ≫ t) g =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V f ((t ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc)) ≫ g) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep,
    comp_whiskerRight, Category.assoc]

/-- 概要：代入射の後の射は最後の合成の後にまとめられる（Berger–Moerdijk §1）。
方針：合成の結合則を使う。
規約：最後の対象の後の射は任意。
使われ方：二入力の合成で出力 arity の移送を末尾に置く。 -/
lemma tensorSubstitutionStep_post {R R' V L O O' : Complex A}
    (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) (h : O ⟶ O') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f (g ≫ h) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g ≫ h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
