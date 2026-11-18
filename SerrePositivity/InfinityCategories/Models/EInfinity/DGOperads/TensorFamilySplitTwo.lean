module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionMiddle

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の末尾二因子の分離

概要：Berger–Moerdijk §1 の反復合成の最後の二入力を、まとめて代入する射として表す。
方針：最後の因子の分離を二回合成し、二段のテンソル代入の結合則を適用する。
規約：前半の入力の順序と、末尾二入力の左から右への順序を保つ。
使われ方：全入力への合成の外側等変性で末尾二入力の交換を二位置への合成へ帰着する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily

/-- 概要：有限テンソル族の最後の二因子を一つの対として分離する（Berger–Moerdijk §1）。
方針：最後の因子を二回分離して結合子で末尾二因子を括る。
規約：前半の入力は二回の castSucc で指定する。
使われ方：二つの末尾入力への代入をまとめた射の始域を与える。 -/
def tensorFamilySplitLastTwo (n : ℕ) (V : Fin (n + 2) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) V ≅
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc) ⊗
        (V (Fin.last n).castSucc ⊗ V (Fin.last (n + 1))) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) V ≪≫
    whiskerRightIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.castSucc)) (V (Fin.last (n + 1))) ≪≫
      α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc))
        (V (Fin.last n).castSucc) (V (Fin.last (n + 1)))

/-- 概要：有限族の二段の末尾への代入は末尾二因子をまとめた代入と一致する（Berger–Moerdijk §1）。
方針：残りの因子の分離を自然性で移し、二段のテンソル代入の結合則を使う。
規約：最後の入力を先に代入し、その前の入力を次に代入する。
使われ方：反復合成の二段を任意の二位置への合成射と比較する。 -/
@[reassoc]
lemma tensorFamilySubstitutionStep_two (n : ℕ) (V : Fin (n + 2) → Complex A)
    {R R₁ R₂ O : Complex A} (f : R ⊗ V (Fin.last (n + 1)) ⟶ R₁)
    (g : R₁ ⊗ V (Fin.last n).castSucc ⟶ R₂)
    (h : R₂ ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc) ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep (n + 1) V f
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n (fun i => V i.castSucc) g h) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n V).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g) h := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo, Iso.trans_hom, whiskerRightIso_hom,
    tensorHom_id, whiskerLeft_comp, Category.assoc]

/-- 概要：有限族の代入射の後の合成を最後の係数射へ移す（Berger–Moerdijk §1）。
方針：射の合成の結合則を使う。
規約：最後の対象の後の射は任意。
使われ方：反復合成の二段の終域の arity の移送をまとめる。 -/
lemma tensorFamilySubstitutionStep_post (n : ℕ) (V : Fin (n + 1) → Complex A)
    {R R' O O' : Complex A} (f : R ⊗ V (Fin.last n) ⟶ R')
    (g : R' ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ O) (h : O ⟶ O') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V f (g ≫ h) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V f g ≫ h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
