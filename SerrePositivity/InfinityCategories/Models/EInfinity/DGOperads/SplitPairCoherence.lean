module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity

/-!
模型。文献の定義との比較は後で
# 二因子の分離と先頭の因子

概要：Berger–Moerdijk §1 の反復合成で用いる二回の分離と結合子を比較する。
方針：任意のモノイダル圏で結合子の自然性と pentagon を適用する。
規約：先頭の因子 R と末尾の対 U,V の順序を保つ。
使われ方：複体の有限テンソル族で末尾二因子の分離の再帰を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 概要：先頭を保つ二回の分離は、尾で二因子を括ってから先頭を分離する射と一致する（Berger–Moerdijk §1）。
方針：二回目の分離を結合子の自然性で移し、四因子の pentagon を使う。
規約：f は最後の因子、g はその前の因子を分離する。
使われ方：有限テンソルの末尾二因子の分離を先頭に関して再帰する。 -/
lemma splitPair_whiskerLeft (R : C) {X Y L U V : C}
    (f : X ⟶ Y ⊗ V) (g : Y ⟶ L ⊗ U) :
    (R ◁ f) ≫ (α_ R Y V).inv ≫
        (((R ◁ g) ≫ (α_ R L U).inv) ▷ V) ≫ (α_ (R ⊗ L) U V).hom =
      (R ◁ (f ≫ (g ▷ V) ≫ (α_ L U V).hom)) ≫ (α_ R L (U ⊗ V)).inv := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionAssociator_four_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- 概要：二回の分離の整合性を分離同型の合成で表す（Berger–Moerdijk §1）。
方針：同型の合成の射を展開し、射に対する整合性を適用する。
規約：二つの分離同型は尾の対象にのみ作用する。
使われ方：複体の再帰的な分離同型へ、括弧の構造を保って適用する。 -/
lemma splitPairIso_whiskerLeft (R : C) {X Y L U V : C}
    (f : X ≅ Y ⊗ V) (g : Y ≅ L ⊗ U) :
    ((whiskerLeftIso R f ≪≫ (α_ R Y V).symm) ≪≫
      whiskerRightIso (whiskerLeftIso R g ≪≫ (α_ R L U).symm) V ≪≫
        α_ (R ⊗ L) U V).hom =
      (R ◁ (f ≪≫ whiskerRightIso g V ≪≫ α_ L U V).hom) ≫
        (α_ R L (U ⊗ V)).inv := by
  simpa only [Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.symm_hom, Category.assoc] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.splitPair_whiskerLeft R f.hom g.hom

/-- 概要：右の二対象の等式による移送は逆結合子と両立する（Berger–Moerdijk §1）。
方針：二つの対象の等式で置き換えて恒等射の式に帰着する。
規約：先頭の対象 R は固定する。
使われ方：末尾二因子の交換後の終域の同定を先頭との括弧の移動に通す。 -/
lemma associator_inv_eqToHom_pair (R : C) {S S' T T' : C}
    (hs : S = S') (ht : T = T') :
    (R ◁ eqToHom (congrArg₂ (fun X Y : C => X ⊗ Y) hs ht)) ≫
        (α_ R S' T').inv =
      (α_ R S T).inv ≫
        eqToHom (congrArg₂ (fun X Y : C => (R ⊗ X) ⊗ Y) hs ht) := by
  subst S'
  subst T'
  simp only [eqToHom_refl, whiskerLeft_id, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
