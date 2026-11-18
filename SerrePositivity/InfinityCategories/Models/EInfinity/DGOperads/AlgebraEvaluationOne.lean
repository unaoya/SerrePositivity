module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraActionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationTensorOne
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
模型。文献の定義との比較は後で
# 一入力の全合成と代数での評価

概要：Berger–Moerdijk §1 の代数で、一入力の全合成の評価と作用の合成を比較する。
方針：標準の代入から単位入力族を除き、部分合成則と右単位子の自然性を使う。
規約：内側演算の arity は零を含む。
使われ方：自由代数の評価射の作用保存に必要な全合成の評価式の基底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一入力の外側への代入は演算の出力に右単位因子を添える射である（Berger–Moerdijk §1）。
方針：先頭への代入の式を用い、長さ零の尾の単位子を相殺する。
規約：入力の 0+n への移送を明示的に前合成する。
使われ方：代数の一入力の部分合成則を通常の射の合成へ戻す。 -/
lemma tensorInsertionAction_only (X C : Complex A) (n : ℕ) (θ : C ⊗ power X n ⟶ X) :
    (C ◁ eqToHom (congrArg (power X) (Nat.zero_add n).symm)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C 0 n 0 θ = θ ≫ (ρ_ X).inv := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]
  simp only [← whiskerLeft_comp_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have hi : (appendIso X n 0).inv = (ρ_ (power X n)).inv := by
    apply (cancel_mono (appendIso X n 0).hom).1
    rw [Iso.inv_hom_id, appendIso_zero_right, Iso.inv_hom_id]
  rw [hi]
  have h : (C ◁ (ρ_ (power X n)).inv) ≫
      (α_ C (power X n) (𝟙_ (Complex A))).inv = (ρ_ (C ⊗ power X n)).inv := by
    monoidal_coherence
  erw [reassoc_of% h, ← rightUnitor_inv_naturality]

namespace Operad.Algebra

variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：一入力の外側と任意の内側の部分合成は作用の合成に評価される（Berger–Moerdijk §1）。
方針：arity の移送を含む部分合成則から、空の前半と末尾の入力を除く。
規約：外側の入力テンソル冪の単位因子は右単位子で補う。
使われ方：一入力の全合成の評価式へ適用する。 -/
lemma unary_comp_action (X : P.Algebra) (n : ℕ) :
    ((P.comp 0 n 0 ≫ eqToHom (congrArg P.arity (Nat.zero_add n))) ▷
      power X.carrier n) ≫ X.action n =
    (α_ (P.arity 1) (P.arity n) (power X.carrier n)).hom ≫
      (P.arity 1 ◁ (X.action n ≫ (ρ_ X.carrier).inv)) ≫ X.action 1 := by
  have h := X.comp_action_transport 0 n 0 (r := 1) rfl (Nat.zero_add n)
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id] at h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_only] at h
  exact h

/-- 概要：一入力の全合成を代数で評価すると内側、外側の順の作用に一致する（Berger–Moerdijk §1）。
方針：Schur 演算の一次の式と部分合成の評価を使い、右単位子の自然性で整理する。
規約：この式は任意の P 代数について成立し、評価射の作用保存を仮定しない。
使われ方：全入力の評価式を有限族の長さで証明する際の一次の計算となる。 -/
lemma schurOperationTensor_action_one (X : P.Algebra) (s : Fin 1 → ℕ) :
    P.schurOperationTensor X.carrier 1 s ≫ X.action (∑ i, s i) =
    (P.arity 1 ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
      (fun r => P.arity r ⊗ power X.carrier r) X.action 1 s) ≫ X.action 1 := by
  rw [P.schurOperationTensor_one]
  simp only [Category.assoc]
  erw [X.action_index_eq (by simp : s 0 = ∑ i, s i)]
  simp only [tensorHom_id]
  rw [X.unary_comp_action]
  simp only [Iso.inv_hom_id_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, tensorHom_id, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily]

end Operad.Algebra

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
