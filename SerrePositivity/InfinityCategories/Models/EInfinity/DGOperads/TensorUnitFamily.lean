module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# テンソル単位の有限族の縮約

概要：Berger–Moerdijk §1 の全合成の右単位則で、各入力へ入れたテンソル単位を一つへ縮約する。
方針：反復合成と同じく最後の因子から縮約する同型を構成する。
規約：空の族の縮約はテンソル単位の恒等同型。
使われ方：全入力へ単位演算を代入した係数射を右単位子へ比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

/-- 概要：テンソル単位の有限テンソル族を一つのテンソル単位へ縮約する同型（Berger–Moerdijk §1）。
方針：最後の因子を分離し、前半を再帰的に縮約して右単位子を適用する。
規約：複体のテンソル構造は既存のものを使う。
使われ方：反復合成で全ての内側演算が単位の場合を計算する。 -/
def tensorUnitFamilyIso (A : Type u) [CommRing A] : ∀ n : ℕ,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun _ => 𝟙_ (Complex A)) ≅ 𝟙_ (Complex A)
  | 0 => Iso.refl _
  | n + 1 => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun _ => 𝟙_ (Complex A)) ≪≫
      tensorIso (tensorUnitFamilyIso A n) (Iso.refl (𝟙_ (Complex A))) ≪≫
      ρ_ (𝟙_ (Complex A))

/-- 概要：単位族の縮約は最後の分離と前半の縮約からなる（Berger–Moerdijk §1）。
方針：同型の定義の射成分を計算する。
規約：右端の単位因子は前半の縮約後まで残す。
使われ方：単位族の縮約と反復合成の再帰を同じ形で比較する。 -/
lemma tensorUnitFamilyIso_succ_hom (A : Type u) [CommRing A] (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A (n + 1)).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun _ => 𝟙_ (Complex A))).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom ▷ 𝟙_ (Complex A)) ≫ (ρ_ (𝟙_ (Complex A))).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
