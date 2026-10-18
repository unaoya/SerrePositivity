module

public import SerrePositivity.EInfinity.Operad.TensorSubstitutionBlocks
public import SerrePositivity.EInfinity.Operad.TensorFamilySplitAt

/-!
# 有限入力族の二ブロックへの代入

概要：Berger–Moerdijk §1 の反復合成の二ブロック分解の帰納段階を処理する。
方針：最後の因子を分離し、後半全体の代入と末尾からの二段の代入を比較する。
規約：前半 n 個、後半 m+1 個の入力の順序を保つ。
使われ方：係数側の反復合成のブロック分解を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  tensorSubstitutionStep tensorFamilySubstitutionStep tensorFamilySplitLast

/-- 概要：有限族への代入の後の射は最終的な出力へ後合成できる（Berger–Moerdijk §1）。
方針：分離と代入の定義で合成の結合則を用いる。
規約：出力の arity の移送も任意の複体射として扱う。
使われ方：入力ブロックごとの総 arity の移送を一つにまとめる。 -/
lemma tensorFamilySubstitutionStep_post (n : ℕ) (V : Fin (n + 1) → Complex A)
    {R R₁ O O' : Complex A} (f : R ⊗ V (Fin.last n) ⟶ R₁)
    (g : R₁ ⊗ tensorFamily n (fun j => V j.castSucc) ⟶ O) (q : O ⟶ O') :
    tensorFamilySubstitutionStep n V f (g ≫ q) =
      tensorFamilySubstitutionStep n V f g ≫ q := by
  unfold tensorFamilySubstitutionStep tensorSubstitutionStep
  simp only [Category.assoc]

/-- 概要：末尾からの二段の代入は、後半の有限族をまとめた代入に一致する（Berger–Moerdijk §1）。
方針：二部分への分離の再帰を展開し、テンソル代入のブロック比較を適用する。
規約：f は最後の因子、g は後半の残り、h は前半の代入を表す。
使われ方：任意の長さの後半への反復合成を前半の合成と接続する。 -/
lemma tensorFamilySubstitutionStep_splitAt (n m : ℕ) (V : Fin (n + m + 1) → Complex A)
    {R R₁ R₂ O : Complex A}
    (f : R ⊗ V (Fin.last (n + m)) ⟶ R₁)
    (g : R₁ ⊗ tensorFamily m (fun j => V (j.natAdd n).castSucc) ⟶ R₂)
    (h : R₂ ⊗ tensorFamily n (fun j => V (j.castAdd (m + 1))) ⟶ O) :
    tensorFamilySubstitutionStep (n + m) V f
      ((R₁ ◁ (tensorFamilySplitAt n m (fun j => V j.castSucc)).hom) ≫
        tensorSubstitutionStep g h) =
    (R ◁ (tensorFamilySplitAt n (m + 1) V).hom) ≫
      tensorSubstitutionStep
        (tensorFamilySubstitutionStep m (fun j => V (j.natAdd n)) f g) h := by
  unfold tensorFamilySubstitutionStep
  simp only [tensorFamilySplitAt, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, whiskerLeftIso_hom]
  conv_rhs =>
    rw [whiskerLeft_comp_assoc]
    arg 2
    erw [tensorSubstitutionStep_blocks]

end SerrePositivity.EInfinity
