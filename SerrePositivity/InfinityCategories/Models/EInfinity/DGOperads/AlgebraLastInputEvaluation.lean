module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraActionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCoreBlocks

/-!
模型。文献の定義との比較は後で
# 反復合成の最後の入力の代数での評価

概要：Berger–Moerdijk §1 の最後の指定入力への部分合成を、前半と新しい末尾の入力上で評価する。
方針：添字を移した代数の部分合成則と三ブロック上での代入の式を使う。
規約：新しい末尾は最後の演算の入力、元の末尾の順序で並ぶ。
使われ方：末尾を残した全合成の評価の帰納段階で係数の部分合成を作用へ変える。
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

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の指定入力への合成は内側作用を先に行うブロック上の射として評価される（Berger–Moerdijk §1）。
方針：新しい末尾の長さの移送を相殺し、三ブロック上での代入へ帰着する。
規約：最後の演算の arity l と元の末尾入力数 k は零を許す。
使われ方：係数と入力を同時に扱う反復合成の評価の帰納段階に用いる。 -/
lemma composeFirstInputInsertion_action_on_blocks (X : P.Algebra) (n k l : ℕ) :
    (P.composeFirstInputInsertion n k l ⊗ₘ
      ((power X.carrier n ◁ ((appendIso X.carrier l k).hom ≫
        eqToHom (congrArg (power X.carrier) (Nat.add_comm l k)))) ≫
        (appendIso X.carrier n (k + l)).hom)) ≫ X.action (n + (k + l)) =
    (α_ (P.arity (n + 1 + k)) (P.arity l)
      (power X.carrier n ⊗ (power X.carrier l ⊗ power X.carrier k))).hom ≫
      (P.arity (n + 1 + k) ◁
        ((α_ (P.arity l) (power X.carrier n)
          (power X.carrier l ⊗ power X.carrier k)).inv ≫
        ((β_ (P.arity l) (power X.carrier n)).hom ▷
          (power X.carrier l ⊗ power X.carrier k)) ≫
        (α_ (power X.carrier n) (P.arity l)
          (power X.carrier l ⊗ power X.carrier k)).hom ≫
        (power X.carrier n ◁
          (α_ (P.arity l) (power X.carrier l) (power X.carrier k)).inv) ≫
        (power X.carrier n ◁ (X.action l ▷ power X.carrier k)) ≫
        (appendIso X.carrier n (k + 1)).hom ≫
        eqToHom (congrArg (power X.carrier)
          (by omega : n + (k + 1) = n + 1 + k)))) ≫ X.action (n + 1 + k) := by
  have hi : (power X.carrier n ◁ ((appendIso X.carrier l k).hom ≫
      eqToHom (congrArg (power X.carrier) (Nat.add_comm l k)))) ≫
      (appendIso X.carrier n (k + l)).hom ≫
      eqToHom (congrArg (power X.carrier) (by omega : n + (k + l) = n + (l + k))) =
      (power X.carrier n ◁ (appendIso X.carrier l k).hom) ≫
        (appendIso X.carrier n (l + k)).hom := by
    simp only [whiskerLeft_comp, Category.assoc]
    rw [appendIso_index_right_assoc X.carrier n (Nat.add_comm l k)]
    simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [tensorHom_def', Category.assoc, X.composeFirstInputInsertion_action,
    associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [hi]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore_on_blocks X.carrier (P.arity l) n l k (X.action l))]
  simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
