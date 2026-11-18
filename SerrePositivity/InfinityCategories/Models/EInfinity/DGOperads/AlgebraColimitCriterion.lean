module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionBaseNaturality

/-!
模型。文献の定義との比較は後で
# 共同全射な入力の族による代数公理の判定

概要：Berger–Moerdijk §1 の代数公理を、各係数付きテンソル冪の共同全射族で判定する。
方針：演算を保つ構造射から、置換・単位・代入の自然性で各公理を移す。
規約：構造射自体の全射性ではなく、係数付きテンソル冪での共同全射性を使う。
使われ方：底の sifted 余極限上に代数構造を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {J : Type v}
  (X : Complex A) (B : J → P.Algebra) (p : ∀ j, (B j).carrier ⟶ X)
  (action : ∀ n, P.arity n ⊗ power X n ⟶ X)
  (hcomm : ∀ j n, (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (p j) n) ≫ action n =
    (B j).action n ≫ p j)
  (hjoint : ∀ (Q : Complex A) (n : ℕ) {T : Complex A}
    (f g : Q ⊗ power X n ⟶ T),
    (∀ j, (Q ◁ _root_.SerrePositivity.TensorPowers.map (p j) n) ≫ f =
      (Q ◁ _root_.SerrePositivity.TensorPowers.map (p j) n) ≫ g) → f = g)

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

include hcomm hjoint

/-- 概要：共同全射な入力の後で等変性を判定する（BM §1）。
方針：テンソル冪の置換の自然性と各代数の等変性を使う。
規約：全ての入力置換を含む。
使われ方：余極限上の代数の等変性を検証する。 -/
lemma epic_equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction X n σ).asIso.hom) ≫ action n = action n := by
  apply hjoint (P.arity n) n
  intro j
  erw [whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality A (p j) n σ,
    ← tensorHom_comp_whiskerLeft_assoc, hcomm]
  rw [← Category.assoc, (B j).equivariance]

/-- 概要：共同全射な入力の後で単位則を判定する（BM §1）。
方針：単位子と一次テンソル冪の比較の自然性を使う。
規約：入力側の固定係数はテンソル単位。
使われ方：余極限上の代数の単位則を検証する。 -/
lemma epic_unit :
    (P.unit ▷ power X 1) ≫ action 1 = (λ_ (power X 1)).hom ≫ (oneIso X).hom := by
  apply hjoint (𝟙_ (Complex A)) 1
  intro j
  rw [whisker_exchange_assoc, hcomm, reassoc_of% ((B j).unit_action),
    leftUnitor_naturality_assoc, oneIso_naturality]

/-- 概要：共同全射な入力の後で全位置の合成則を判定する（BM §1）。
方針：代入の底の射についての自然性で各代数の合成則へ戻す。
規約：内側の零入力演算も許す。
使われ方：余極限上の代数の合成則を検証する。 -/
lemma epic_composition (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ power X (m + n)) ≫ action (m + n) =
      (α_ (P.arity (m + 1)) (P.arity n) (power X (m + n))).hom ≫
        (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (P.arity n) m n i (action n)) ≫
        action (m + 1) := by
  apply hjoint (P.arity (m + 1) ⊗ P.arity n) (m + n)
  intro j
  rw [whisker_exchange_assoc, hcomm, ← Category.assoc, (B j).comp_action]
  simp only [Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_base_naturality (p j) m n i _ _ (hcomm j n)]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hcomm]

/-- 概要：共同全射な入力の族から代数公理を構成する（BM §1）。
方針：各公理を係数付きテンソル冪の族の前合成後に判定する。
規約：arity 0 の演算も含む。
使われ方：sifted 余極限へ降りた作用を実際の代数に束ねる。 -/
def ofJointlyEpicActions : P.Algebra where
  carrier := X
  action := action
  equivariance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.epic_equivariance X B p action hcomm hjoint
  unit_action := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.epic_unit X B p action hcomm hjoint
  comp_action := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.epic_composition X B p action hcomm hjoint

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
