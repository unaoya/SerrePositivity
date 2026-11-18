module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionBaseNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
模型。文献の定義との比較は後で
# 演算保存の部分合成による伝播

概要：二つの arity の作用を保つ底の射は、全射な部分合成の出力の作用も保つ。
方針：元の両代数の合成則と入力代入の自然性を使い、係数の全射を相殺する。
規約：元の底の射と全入力位置を保持する。
使われ方：Com の全作用保存を零入力・二入力から得る。
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
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

lemma actionHom_of_composition (X Y : P.Algebra) (f : X.carrier ⟶ Y.carrier)
    (m n : ℕ) (i : Fin (m + 1))
    [Epi (P.comp m n i ▷ power X.carrier (m + n))]
    (hm : X.action (m + 1) ≫ f =
      (P.arity (m + 1) ◁ _root_.SerrePositivity.TensorPowers.map f (m + 1)) ≫ Y.action (m + 1))
    (hn : X.action n ≫ f = (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map f n) ≫ Y.action n) :
    X.action (m + n) ≫ f =
      (P.arity (m + n) ◁ _root_.SerrePositivity.TensorPowers.map f (m + n)) ≫ Y.action (m + n) := by
  apply (cancel_epi (P.comp m n i ▷ power X.carrier (m + n))).mp
  have hx := congrArg (fun g => g ≫ f) (X.comp_action m n i)
  simp only [Category.assoc, hm] at hx
  rw [← whiskerLeft_comp_assoc,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_base_naturality f m n i _ _ hn.symm] at hx
  simp only [whiskerLeft_comp, Category.assoc] at hx
  rw [← associator_naturality_right_assoc, ← Y.comp_action,
    whisker_exchange_assoc] at hx
  exact hx

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
