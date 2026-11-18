module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition

/-!
模型。文献の定義との比較は後で
# Schur 入力の生成射の自然性

概要：Berger–Moerdijk §1 の自由代数の入力の生成射が底の複体射と両立することを示す。
方針：一般の生成射の有限テンソルについて射族の可換性を帰納的にテンソルする。
規約：全ての入力には同じ底の複体射を適用する。
使われ方：Schur 対象上の作用射の自然性と自由代数関手の射の保存則に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：生成射の有限テンソルは生成射族の可換な射と両立する（Berger–Moerdijk §1）。
方針：先頭の入力の可換性と残りの族の帰納仮定をテンソルする。
規約：生成射の添字型は任意の小さい型とする。
使われ方：Schur 入力の生成射の自然性を各 arity の自然性から導く。 -/
lemma tensorFamilyGenerator_naturality {I : Type} {X Y : Complex A}
    (D E : I → Complex A) (e : ∀ i, D i ⟶ X) (f : ∀ i, E i ⟶ Y)
    (g : X ⟶ Y) (h : ∀ i, D i ⟶ E i) (he : ∀ i, e i ≫ g = h i ≫ f i)
    (n : ℕ) (s : Fin n → I) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s ≫ _root_.SerrePositivity.TensorPowers.map g n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => h (s i)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator Y E f n s := by
  induction n with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n ih =>
    change (e (s 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun i => s i.succ)) ≫
      (g ⊗ₘ _root_.SerrePositivity.TensorPowers.map g n) =
        (h (s 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => h (s i.succ))) ≫
          (f (s 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator Y E f n (fun i => s i.succ))
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, he, ih]

namespace Operad

/-- 概要：Schur 入力の生成射は底の複体射に関して自然である（Berger–Moerdijk §1）。
方針：各 arity の Schur 生成射の自然性を有限テンソルする。
規約：内側 arity の族は固定する。
使われ方：生成射上の自然性から自由代数の作用射の自然性を得る。 -/
lemma schurInputGenerator_naturality (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K L : Complex A} (f : K ⟶ L)
    (n : ℕ) (s : Fin n → ℕ) :
    P.schurInputGenerator K n s ≫ _root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f) n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => 𝟙 (P.arity (s i)) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f (s i)) ≫
        P.schurInputGenerator L n s := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_naturality
    (fun i => P.arity i ⊗ power K i) (fun i => P.arity i ⊗ power L i)
    (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K i) (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence L i)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f) (fun i => 𝟙 (P.arity i) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f i)
    (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality A P.sequence f i) n s

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
