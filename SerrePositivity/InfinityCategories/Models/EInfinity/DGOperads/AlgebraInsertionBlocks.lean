module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCoreBlocks

/-!
模型。文献の定義との比較は後で
# 三ブロックの入力上での代数の部分合成則

概要：Berger–Moerdijk §1 の部分合成の評価を、前方・内側・後方の入力を分けて記述する。
方針：部分合成公理を使い、標準の代入射を三ブロック上で計算する式へ置き換える。
規約：入力の順序を保ち、係数の移動には Koszul 対称性を使う。
使われ方：全合成の評価の帰納段階で最後の内側の作用を取り出す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：部分合成を三ブロックの入力で評価すると中間ブロックの作用を先に行える（Berger–Moerdijk §1）。
方針：代数の部分合成公理へ入力の連結を前合成し、代入のブロック上の式を用いる。
規約：中間ブロックの arity n は零でもよい。
使われ方：係数の反復合成の再帰を、内側の作用の反復へ変換する。 -/
lemma comp_action_on_blocks (X : P.Algebra) (s n t : ℕ) :
    (P.comp (s + t) n ⟨s, by omega⟩ ⊗ₘ
      ((power X.carrier s ◁ (appendIso X.carrier n t).hom) ≫
        (appendIso X.carrier s (n + t)).hom ≫
        eqToHom (congrArg (power X.carrier)
          (by omega : s + (n + t) = s + t + n)))) ≫ X.action (s + t + n) =
    (α_ (P.arity (s + t + 1)) (P.arity n)
      (power X.carrier s ⊗ (power X.carrier n ⊗ power X.carrier t))).hom ≫
      (P.arity (s + t + 1) ◁
        ((α_ (P.arity n) (power X.carrier s)
          (power X.carrier n ⊗ power X.carrier t)).inv ≫
        ((β_ (P.arity n) (power X.carrier s)).hom ▷
          (power X.carrier n ⊗ power X.carrier t)) ≫
        (α_ (power X.carrier s) (P.arity n)
          (power X.carrier n ⊗ power X.carrier t)).hom ≫
        (power X.carrier s ◁
          (α_ (P.arity n) (power X.carrier n) (power X.carrier t)).inv) ≫
        (power X.carrier s ◁ (X.action n ▷ power X.carrier t)) ≫
        (appendIso X.carrier s (t + 1)).hom ≫
        eqToHom (congrArg (power X.carrier)
          (by omega : s + (t + 1) = s + t + 1)))) ≫ X.action (s + t + 1) := by
  rw [tensorHom_def', Category.assoc, X.comp_action, associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_on_blocks]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
