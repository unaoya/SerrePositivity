module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の生成射による一意性

概要：Berger–Moerdijk §1 の自由代数の生成射の議論に用いる、有限テンソルの一般補題。
方針：一因子についての一意性を、結合子で前の固定因子をまとめながら帰納的に適用する。
規約：生成射の一意性は明示的な数学的仮定。Schur の場合は余極限保存で証明して適用する。
使われ方：任意個の Schur 入力を持つ演算の一意性を証明する。
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

/-- 概要：一因子で射を判定する生成射族は有限テンソル冪でも射を判定する（Berger–Moerdijk §1）。
方針：入力数の帰納法で一因子を生成射へ制限し、残りに帰納法を適用する。
規約：一因子の判定は任意の左右の固定テンソル因子に対して要求する。
使われ方：Schur の生成射に適用して自由代数の演算を生成射上で比較する。 -/
lemma tensorFamilyGenerator_hom_ext (X : Complex A) (D : ℕ → Complex A) (e : ∀ i, D i ⟶ X)
    (he : ∀ (C T Y : Complex A) (f g : C ⊗ (X ⊗ T) ⟶ Y),
      (∀ i, (C ◁ (e i ▷ T)) ≫ f = (C ◁ (e i ▷ T)) ≫ g) → f = g)
    (n : ℕ) (C Y : Complex A) (f g : C ⊗ _root_.SerrePositivity.TensorPowers.power X n ⟶ Y)
    (h : ∀ s : Fin n → ℕ, (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s) ≫ f =
      (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s) ≫ g) : f = g := by
  induction n generalizing C with
  | zero =>
    have hs := h Fin.elim0
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, whiskerLeft_id, Category.id_comp] using hs
  | succ n ih =>
    apply he C (_root_.SerrePositivity.TensorPowers.power X n) Y f g
    intro m
    apply (cancel_epi (α_ C (D m) (_root_.SerrePositivity.TensorPowers.power X n)).hom).1
    apply ih (C ⊗ D m)
    intro s
    have hs0 := h (Fin.cons (α := fun _ : Fin (n + 1) => ℕ) m s)
    change (C ◁ (e m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s)) ≫ f =
      (C ◁ (e m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s)) ≫ g at hs0
    have hs := congrArg (fun (t : C ⊗ (D m ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (s i))) ⟶ Y) =>
      (α_ C (D m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (s i)))).hom ≫ t) hs0
    simp only [associator_naturality_right_assoc,
      ← whiskerLeft_comp_assoc, ← tensorHom_def']
    exact hs

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
